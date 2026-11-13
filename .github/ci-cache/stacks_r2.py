"""Signed access to the optional R2 Stacks baseline."""
import json
import os
from pathlib import Path
import re

import checkpoint
from r2_storage import INDEX_BYTES, MAX_ARCHIVE_BYTES, R2Storage

PREFIX_BYTES = 8 * 1024**2
LARGE_PREFIX_BYTES = 16 * 1024**2
RETAINED_GENERATIONS = 2


def preview_bytes(archive_size):
    # Larger checkpoints carry a larger compressed file manifest.
    return min(archive_size, LARGE_PREFIX_BYTES if archive_size >= 2 * 1024**3 else PREFIX_BYTES)


class R2Cache(R2Storage):
    def __init__(self, endpoint, bucket, access_key, secret_key, revision, context):
        super().__init__(endpoint, bucket, access_key, secret_key,
                         f'stacks/v{checkpoint.SCHEMA}/{revision}/{context}')
        self.revision = revision
        self.context = context

    @classmethod
    def configured(cls, revision, context):
        connection = cls.connection()
        if connection is None:
            return None
        if not re.fullmatch(r'[0-9a-f]{40}', revision) or not re.fullmatch(r'[0-9a-f]{64}', context):
            raise ValueError('invalid R2 Stacks revision or context')
        return cls(*connection, revision, context)

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
        dates = {key: date for key, date in self.list_objects(directory, 'objects/')
                 if date and re.fullmatch(r'objects/[0-9a-f]{64}[.]tar[.]zst', key)}
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
        length = preview_bytes(index['size']) if prefix else index['size']
        headers = (f'Range: bytes=0-{length - 1}',) if prefix else ()
        status, _ = self.request('GET', self.archive_key(index), output,
                                 seconds=20 if prefix else 180, headers=headers, limit=length)
        if status != (206 if prefix else 200):
            raise OSError(f'R2 Stacks archive returned HTTP {status}')
        if output.stat().st_size != length:
            raise ValueError('R2 Stacks archive size mismatch')
        if not prefix and checkpoint.file_hash(output) != index['sha256']:
            raise ValueError('R2 Stacks archive digest mismatch')

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
