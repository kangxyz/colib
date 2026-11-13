"""Signed access to the optional R2 Stacks baseline."""
import json
import os
from pathlib import Path
import re
import subprocess
from urllib.parse import urlencode
from xml.etree import ElementTree

import checkpoint

PREFIX_BYTES = 8 * 1024**2
INDEX_BYTES = 8192
# R2's single-request upload limit is 5 GiB minus 5 MiB.
MAX_ARCHIVE_BYTES = 5 * 1024**3 - 5 * 1024**2
WRITE_CONFLICT = (409, 412)
RETAINED_GENERATIONS = 2


class R2Cache:
    def __init__(self, endpoint, bucket, access_key, secret_key, revision, context):
        self.url = f'{endpoint}/{bucket}'
        self.credentials = f'{access_key}:{secret_key}'
        self.revision = revision
        self.context = context
        self.prefix = f'stacks/v{checkpoint.SCHEMA}/{revision}/{context}'

    @classmethod
    def configured(cls, revision, context):
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
        if not re.fullmatch(r'[0-9a-f]{40}', revision) or not re.fullmatch(r'[0-9a-f]{64}', context):
            raise ValueError('invalid R2 Stacks revision or context')
        return cls(endpoint, bucket, access_key, secret_key, revision, context)

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

    def current(self, output):
        status, etag = self.request('GET', 'current.json', output, seconds=15, limit=INDEX_BYTES)
        if status == 404:
            return None, None
        if status != 200:
            raise OSError(f'R2 current.json returned HTTP {status}')
        index = json.loads(output.read_bytes())
        if (not isinstance(index, dict) or index.get('schema') != 1
                or index.get('revision') != self.revision or index.get('context') != self.context
                or type(index.get('size')) is not int or not 0 < index['size'] <= MAX_ARCHIVE_BYTES
                or any(not isinstance(index.get(key), str) or not re.fullmatch(r'[0-9a-f]{64}', index[key])
                       for key in ('sha256', 'generation'))
                or not re.fullmatch(r'"[0-9a-fA-F]+"', etag)):
            raise ValueError('invalid R2 Stacks index')
        previous = index.get('previous_generation')
        if previous is not None and (not isinstance(previous, str)
                                     or not re.fullmatch(r'[0-9a-f]{64}', previous)
                                     or previous == index['generation']):
            raise ValueError('invalid R2 previous Stacks generation')
        return index, etag

    def prune_archives(self, directory):
        current_file = directory / 'retained-current.json'
        current, etag = self.current(current_file)
        if current is None:
            return
        live = self.archive_key(current)
        prefix = self.prefix + '/objects/'
        parameters = {'list-type': 2, 'prefix': prefix}
        archived = []
        listing = directory / 'r2-objects.xml'
        while True:
            status, _ = self.request('GET', '', listing, seconds=20, query=parameters)
            if status != 200:
                raise OSError(f'R2 ListObjectsV2 returned HTTP {status}')
            try:
                objects = ElementTree.parse(listing).getroot()
            except ElementTree.ParseError as error:
                raise ValueError('invalid R2 object listing') from error
            for item in objects.findall('{*}Contents'):
                key = item.findtext('{*}Key', '').removeprefix(self.prefix + '/')
                date = item.findtext('{*}LastModified', '')
                if date and re.fullmatch(r'objects/[0-9a-f]{64}[.]tar[.]zst', key):
                    archived.append((date, key))
            if objects.findtext('{*}IsTruncated') != 'true':
                break
            marker = objects.findtext('{*}NextContinuationToken')
            if not marker or marker == parameters.get('continuation-token'):
                raise ValueError('invalid R2 object listing continuation')
            parameters['continuation-token'] = marker
        dates = {key: date for date, key in archived}
        if live not in dates or not dates[live]:
            raise ValueError('R2 current checkpoint is missing in its object listing')
        # Objects newer than the live archive can belong to an in-flight publisher.
        older = sorted(((date, key) for key, date in dates.items()
                        if key != live and date <= dates[live]), reverse=True)
        previous = current.get('previous_generation')
        if previous is not None:
            previous = self.archive_key({'generation': previous})
            if previous not in dates:
                raise ValueError('R2 previous Stacks checkpoint is missing in its object listing')
        elif older:
            previous = older[0][1]
        for _, key in older:
            if key == previous:
                continue
            latest, latest_etag = self.current(current_file)
            if latest_etag != etag or latest != current:
                print('R2 Stacks baseline advanced during pruning. Leaving remaining archives.', flush=True)
                return
            status, _ = self.request('DELETE', key, Path(os.devnull), seconds=20)
            if status != 204:
                raise OSError(f'R2 could not delete obsolete Stacks archive {key} (HTTP {status})')
            print(f'Pruned obsolete R2 Stacks archive {key}.', flush=True)

    @staticmethod
    def archive_key(index):
        return f"objects/{index['generation']}.tar.zst"

    def download(self, index, output, *, prefix=False):
        length = min(PREFIX_BYTES, index['size']) if prefix else index['size']
        headers = (f'Range: bytes=0-{length - 1}',) if prefix else ()
        status, _ = self.request('GET', self.archive_key(index), output,
                                 seconds=20 if prefix else 180, headers=headers, limit=length)
        if status != (206 if prefix else 200):
            raise OSError(f'R2 Stacks archive returned HTTP {status}')
        if output.stat().st_size != length:
            raise ValueError('R2 Stacks archive size mismatch')
        if not prefix and checkpoint.file_hash(output) != index['sha256']:
            raise ValueError('R2 Stacks archive digest mismatch')

    def put(self, key, source, digest, condition, *, seconds, metadata=()):
        status, _ = self.request('PUT', key, Path(os.devnull), seconds=seconds, upload=source,
                                 headers=(condition, f'x-amz-content-sha256: {digest}', *metadata))
        if status == 200 or status in WRITE_CONFLICT:
            return status
        raise OSError(f'R2 PUT {key} returned HTTP {status}')

    def store_archive(self, index, source):
        key = self.archive_key(index)
        digest = index['sha256']
        status = self.put(key, source, digest, 'If-None-Match: *', seconds=240,
                          metadata=(f'x-amz-meta-sha256: {digest}',))
        if status == 200:
            return index
        if status == 409:
            return None
        # A concurrent publisher may have used different tar bytes for the
        # same generated files. Point to the bytes that won the conditional PUT.
        status, fields = self.request('HEAD', key, Path(os.devnull), seconds=15,
                                      response_headers=('content-length', 'x-amz-meta-sha256'))
        if status != 200:
            raise OSError(f'R2 could not verify the existing Stacks archive (HTTP {status})')
        size, _, digest = fields.partition('\n')
        if (not size.isdecimal() or not 0 < int(size) <= MAX_ARCHIVE_BYTES
                or not re.fullmatch(r'[0-9a-f]{64}', digest)):
            raise ValueError('invalid metadata on the existing R2 Stacks archive')
        return dict(index, size=int(size), sha256=digest)
