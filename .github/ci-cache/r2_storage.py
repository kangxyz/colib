"""Signed S3 transport for the private CI cache bucket."""
import json
import os
from pathlib import Path
import re
import subprocess
from urllib.parse import urlencode
from xml.etree import ElementTree

INDEX_BYTES = 8192
# R2's single-request upload limit is 5 GiB minus 5 MiB.
MAX_ARCHIVE_BYTES = 5 * 1024**3 - 5 * 1024**2
WRITE_CONFLICT = (409, 412)


class R2Storage:
    def __init__(self, endpoint, bucket, access_key, secret_key, prefix):
        self.url = f'{endpoint}/{bucket}'
        self.credentials = f'{access_key}:{secret_key}'
        self.prefix = prefix

    @staticmethod
    def connection():
        endpoint = os.environ.get('STACKS_R2_ENDPOINT', '').rstrip('/')
        bucket = os.environ.get('STACKS_R2_BUCKET', '')
        access_key = os.environ.get('STACKS_R2_ACCESS_KEY_ID', '')
        secret_key = os.environ.get('STACKS_R2_SECRET_ACCESS_KEY', '')
        if not all((endpoint, bucket, access_key, secret_key)):
            return None
        if not re.fullmatch(r'https://[0-9a-f]{32}(?:\.(?:eu|fedramp|us))?\.r2\.cloudflarestorage\.com',
                            endpoint):
            raise ValueError('invalid R2 S3 endpoint')
        if not re.fullmatch(r'[a-z0-9][a-z0-9-]{1,61}[a-z0-9]', bucket):
            raise ValueError('invalid R2 bucket name')
        return endpoint, bucket, access_key, secret_key

    def request(self, method, key, output, *, seconds, headers=(), upload=None, limit=None,
                response_headers=('etag',), query=None):
        # Feed credentials on stdin so they are absent from process arguments.
        command = ['curl', '--disable', '--silent', '--show-error', '--proto', '=https',
                   '--aws-sigv4', 'aws:amz:auto:s3', '--config', '-', '--request', method,
                   '--connect-timeout', '10', '--max-time', str(seconds),
                   '--output', str(output), '--write-out',
                   '%{http_code}\n' + '\n'.join(f'%header{{{name}}}' for name in response_headers)]
        if method == 'HEAD':
            command.append('--head')
        for header in headers:
            command += ['--header', header]
        if upload is not None:
            command += ['--upload-file', str(upload)]
        if limit is not None:
            command += ['--max-filesize', str(limit)]
        url = f'{self.url}/{self.prefix}/{key}' if query is None else f'{self.url}?{urlencode(query)}'
        result = subprocess.run([*command, url], text=True,
                                input='user = ' + json.dumps(self.credentials) + '\n',
                                capture_output=True)
        if result.returncode:
            raise OSError(f'R2 {method} {key} failed (curl exit {result.returncode})')
        status, _, fields = result.stdout.partition('\n')
        return int(status), fields.strip()

    def put(self, key, source, digest, condition, *, seconds, metadata=()):
        status, _ = self.request('PUT', key, Path(os.devnull), seconds=seconds, upload=source,
                                 headers=(condition, f'x-amz-content-sha256: {digest}', *metadata))
        if status == 200 or status in WRITE_CONFLICT:
            return status
        raise OSError(f'R2 PUT {key} returned HTTP {status}')

    def list_objects(self, directory, prefix):
        scope = self.prefix + '/'
        parameters = {'list-type': 2, 'prefix': scope + prefix}
        listing = directory / 'r2-objects.xml'
        seen = set()
        while True:
            status, _ = self.request('GET', '', listing, seconds=20, query=parameters)
            if status != 200:
                raise OSError(f'R2 ListObjectsV2 returned HTTP {status}')
            try:
                objects = ElementTree.parse(listing).getroot()
            except ElementTree.ParseError as error:
                raise ValueError('invalid R2 object listing') from error
            if objects.tag.split('}')[-1] != 'ListBucketResult':
                raise ValueError('invalid R2 object listing')
            for item in objects.findall('{*}Contents'):
                key = item.findtext('{*}Key', '')
                if key.startswith(scope + prefix):
                    yield key.removeprefix(scope), item.findtext('{*}LastModified', '')
            if objects.findtext('{*}IsTruncated') != 'true':
                break
            marker = objects.findtext('{*}NextContinuationToken')
            if not marker or marker in seen:
                raise ValueError('invalid R2 object listing continuation')
            seen.add(marker)
            parameters['continuation-token'] = marker
