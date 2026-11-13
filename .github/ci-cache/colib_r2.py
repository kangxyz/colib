"""Store and retrieve up to two distinct verified Colib native cache archives."""
from datetime import datetime, timedelta, timezone
import json
import os
from pathlib import Path
import re
import shutil

from checkpoint import file_hash
from r2_storage import INDEX_BYTES, MAX_ARCHIVE_BYTES, R2Storage, WRITE_CONFLICT

RETAINED_GENERATIONS = 2
DOMAIN = re.compile(r'Linux-(?:X64|ARM64)-[0-9a-f]{16}')
COMMIT = re.compile(r'[0-9a-f]{40}')
DIGEST = re.compile(r'[0-9a-f]{64}')
OBJECT = re.compile(r'objects/(Linux-(?:X64|ARM64)-[0-9a-f]{16})/([0-9a-f]{64})[.]tar')


class ColibR2:
    def __init__(self, storage, repository, branch):
        self.storage = storage
        self.repository = repository
        self.branch = branch

    @classmethod
    def configured(cls, repository, branch):
        connection = R2Storage.connection()
        if connection is None:
            return None
        return cls(R2Storage(*connection, 'colib/v1'), repository, branch)

    @staticmethod
    def archive_key(entry):
        return f'objects/{entry["domain"]}/{entry["sha256"]}.tar'

    @staticmethod
    def content_key(entry):
        return entry['domain'], entry['content_sha256']

    @staticmethod
    def order(entry):
        return entry['run_number'], entry['attempt']

    @classmethod
    def validate_entry(cls, entry):
        if (not isinstance(entry, dict) or
                any(not isinstance(entry.get(key), str) or not pattern.fullmatch(entry[key])
                    for key, pattern in (('domain', DOMAIN), ('revision', COMMIT), ('sha256', DIGEST),
                                         ('content_sha256', DIGEST))) or
                any(type(entry.get(key)) is not int or entry[key] <= 0
                    for key in ('size', 'run_id', 'run_number', 'attempt')) or
                entry['size'] > MAX_ARCHIVE_BYTES):
            raise ValueError('invalid Colib R2 archive identity')
        return entry

    def current(self, directory):
        index = directory / 'colib-r2-current.json'
        status, etag = self.storage.request('GET', 'current.json', index, seconds=15, limit=INDEX_BYTES)
        if status == 404:
            return [], None
        if status != 200:
            raise OSError(f'Colib R2 index returned HTTP {status}')
        data = json.loads(index.read_bytes())
        if (not isinstance(data, dict) or type(data.get('schema')) is not int or data['schema'] != 1
                or data.get('repository') != self.repository or data.get('branch') != self.branch
                or not isinstance(data.get('archives'), list)
                or not 1 <= len(data['archives']) <= RETAINED_GENERATIONS
                or not re.fullmatch(r'"[0-9a-fA-F]+"', etag)):
            raise ValueError('invalid Colib R2 index')
        entries = [self.validate_entry(entry) for entry in data['archives']]
        if (entries != sorted(entries, key=self.order, reverse=True)
                or len({self.order(entry) for entry in entries}) != len(entries)
                or len({self.archive_key(entry) for entry in entries}) != len(entries)
                or len({self.content_key(entry) for entry in entries}) != len(entries)):
            raise ValueError('invalid Colib R2 archive order')
        return entries, etag

    def matching(self, domain, directory):
        entries, _ = self.current(directory)
        return [entry for entry in entries if entry['domain'] == domain]

    def download(self, entry, directory):
        if shutil.disk_usage(directory).free < 3 * entry['size'] + 512 * 1024**2:
            raise ValueError('insufficient temporary space for the Colib R2 archive')
        archive = directory / 'lake-native-cache.tar'
        status, _ = self.storage.request('GET', self.archive_key(entry), archive,
                                         seconds=120, limit=entry['size'])
        if status != 200:
            raise OSError(f'Colib R2 archive returned HTTP {status}')
        if archive.stat().st_size != entry['size'] or file_hash(archive) != entry['sha256']:
            raise ValueError('Colib R2 archive size or SHA-256 mismatch')
        return archive

    def store_archive(self, archive, entry, directory):
        key = self.archive_key(entry)
        status = self.storage.put(key, archive, entry['sha256'], 'If-None-Match: *', seconds=180,
                                  metadata=(f'x-amz-meta-sha256: {entry["sha256"]}',))
        if status == 200:
            return True
        if status == 409:
            return False
        observed, fields = self.storage.request('HEAD', key, Path(os.devnull), seconds=15,
                                               response_headers=('content-length', 'x-amz-meta-sha256'))
        size, _, digest = fields.partition('\n')
        if observed != 200 or size != str(entry['size']) or (digest and digest != entry['sha256']):
            raise OSError(f'could not verify the existing Colib R2 archive {key}')
        if not digest:
            # An archive seeded through the Cloudflare API can lack S3 metadata.
            self.download(entry, directory).unlink()
        return True

    def prune(self, directory, entries, etag, removed, started):
        kept = {self.archive_key(entry) for entry in entries}
        # A crashed publication can leave an unindexed archive. Give any current
        # uploads time to commit their index, and protect both current entries.
        cutoff = started - timedelta(hours=1)
        listing = dict(self.storage.list_objects(directory, 'objects/'))
        if not kept <= listing.keys():
            raise OSError('an indexed Colib R2 archive is missing; leaving older archives in place')
        obsolete = set(removed)
        for key, timestamp in listing.items():
            if (OBJECT.fullmatch(key) and timestamp and key not in kept
                    and datetime.fromisoformat(timestamp) < cutoff):
                obsolete.add(key)
        for key in sorted(obsolete - kept):
            _, current_etag = self.current(directory)
            if current_etag != etag:
                return
            status, _ = self.storage.request('DELETE', key, Path(os.devnull), seconds=15)
            if status not in (204, 404):
                raise OSError(f'Colib R2 archive cleanup returned HTTP {status}')
            print(f'Pruned superseded Colib R2 archive {key}.', flush=True)

    def publish(self, archive, entry, directory):
        entry = self.validate_entry(entry)
        if archive.stat().st_size != entry['size'] or file_hash(archive) != entry['sha256']:
            raise ValueError('Colib archive differs from the published Release asset')
        identity = self.content_key(entry)
        index = directory / 'colib-r2-next.json'
        started = datetime.now(timezone.utc)
        uploaded = False
        for _ in range(3):
            entries, etag = self.current(directory)
            if any(self.content_key(candidate) == identity for candidate in entries):
                self.prune(directory, entries, etag, (), started)
                print(f'Colib R2 already has cache content {entry["content_sha256"][:12]}.', flush=True)
                return
            keep = sorted([entry, *entries], key=self.order, reverse=True)[:RETAINED_GENERATIONS]
            if entry not in keep:
                print('Colib R2 already has two newer verified archives.', flush=True)
                return
            if any(self.archive_key(existing) == self.archive_key(entry) for existing in entries):
                raise ValueError('Colib R2 archive key has conflicting content metadata')
            if any(self.order(existing) == self.order(entry) for existing in entries):
                raise ValueError('different Colib archive for an indexed CI run attempt')
            if not uploaded:
                uploaded = self.store_archive(archive, entry, directory)
                if not uploaded:
                    continue
            data = {'schema': 1, 'repository': self.repository, 'branch': self.branch, 'archives': keep}
            index.write_text(json.dumps(data, sort_keys=True) + '\n')
            condition = f'If-Match: {etag}' if etag else 'If-None-Match: *'
            status = self.storage.put('current.json', index, file_hash(index), condition, seconds=20)
            if status in WRITE_CONFLICT:
                continue
            actual, current_etag = self.current(directory)
            if actual != keep:
                print('Colib R2 index advanced before cleanup.', flush=True)
                return
            print(f'Published Colib R2 archive {entry["revision"][:12]} ({entry["size"]} bytes).', flush=True)
            self.prune(directory, keep, current_etag,
                       [self.archive_key(item) for item in entries if item not in keep], started)
            return
        raise OSError('Colib R2 index changed concurrently during publication')
