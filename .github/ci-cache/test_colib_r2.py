"""Exercise Colib backup commits, retention, and download integrity."""

from contextlib import redirect_stdout
from datetime import datetime, timezone
from hashlib import sha256
from io import StringIO
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from checkpoint import file_hash
from colib_r2 import ColibR2


class Bucket:
    def __init__(self):
        self.objects = {}
        self.events = []
        self.interrupt_commit = False

    @staticmethod
    def etag(value):
        return f'"{sha256(value).hexdigest()[:32]}"'

    def request(self, method, key, output, *, seconds, **options):
        self.events.append((method, key))
        if key not in self.objects:
            return 404, ''
        value = self.objects[key]
        if method == 'GET':
            output.write_bytes(value)
            return 200, self.etag(value)
        if method == 'HEAD':
            return 200, str(len(value))
        if method == 'DELETE':
            del self.objects[key]
            return 204, ''
        raise AssertionError(f'Unexpected R2 request {method} {key}')

    def put(self, key, source, digest, condition, *, seconds, metadata=()):
        self.events.append(('PUT', key))
        if digest != file_hash(source):
            raise AssertionError('PUT did not sign its input bytes')
        previous = self.objects.get(key)
        expected = 'If-None-Match: *' if previous is None else f'If-Match: {self.etag(previous)}'
        if condition != expected:
            return 412
        if key == 'current.json' and self.interrupt_commit:
            raise OSError('simulated interruption at index write')
        self.objects[key] = source.read_bytes()
        return 200

    def list_objects(self, directory, prefix):
        return [(key, datetime.now(timezone.utc).isoformat()) for key in self.objects if key.startswith(prefix)]


class ColibBackupTests(unittest.TestCase):
    def setUp(self):
        tmp = TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.directory = Path(tmp.name)
        self.bucket = Bucket()
        self.mirror = ColibR2(self.bucket, 'kangxyz/colib', 'main')
        capture = redirect_stdout(StringIO())
        capture.__enter__()
        self.addCleanup(capture.__exit__, None, None, None)

    def archive(self, number, *, content=None):
        archive = self.directory / f'source-{number}.tar'
        archive.write_bytes(f'ci-native-bytes-from-attempt-{number}'.encode())
        entry = {'revision': f'{number:040x}', 'domain': 'Linux-X64-' + 'a'*16,
                 'sha256': file_hash(archive), 'size': archive.stat().st_size, 'run_id': number + 100,
                 'run_number': number, 'attempt': 1, 'content_sha256': f'{content or number:064x}'}
        return archive, entry

    def test_two_distinct_archives_and_no_reupload_for_same_content(self):
        first, second, third = [self.archive(number) for number in range(1, 4)]
        self.mirror.publish(*first, self.directory)
        self.mirror.publish(*second, self.directory)
        self.bucket.events.clear()
        self.mirror.publish(*third, self.directory)
        oldest = self.mirror.archive_key(first[1])
        self.assertEqual(self.mirror.matching(third[1]['domain'], self.directory), [third[1], second[1]])
        self.assertLess(self.bucket.events.index(('PUT', 'current.json')),
                        self.bucket.events.index(('DELETE', oldest)))
        self.assertEqual(self.mirror.matching('Linux-ARM64-' + 'a'*16, self.directory), [])
        self.assertNotIn(oldest, self.bucket.objects)

        self.bucket.events.clear()
        duplicate = self.archive(4, content=3)
        self.mirror.publish(*duplicate, self.directory)
        self.mirror.publish(*first, self.directory)
        self.assertFalse(any(method == 'PUT' for method, _ in self.bucket.events))
        self.assertEqual(self.mirror.current(self.directory)[0], [third[1], second[1]])

    def test_interrupted_publish_keeps_both_good_archives_and_retry_reuses_upload(self):
        first, second, third = [self.archive(number) for number in range(1, 4)]
        self.mirror.publish(*first, self.directory)
        self.mirror.publish(*second, self.directory)
        original = self.bucket.objects.copy()

        self.bucket.interrupt_commit = True
        with self.assertRaisesRegex(OSError, 'interruption'):
            self.mirror.publish(*third, self.directory)
        for key, data in original.items():
            self.assertEqual(self.bucket.objects[key], data)
        self.assertEqual(self.mirror.current(self.directory)[0], [second[1], first[1]])
        self.assertEqual(self.mirror.download(first[1], self.directory).read_bytes(), first[0].read_bytes())

        self.bucket.interrupt_commit = False
        self.mirror.publish(*third, self.directory)
        self.assertEqual(self.mirror.current(self.directory)[0], [third[1], second[1]])
        self.assertNotIn(self.mirror.archive_key(first[1]), self.bucket.objects)

    def test_corrupt_archive_and_unverified_upload_are_rejected(self):
        archive, entry = self.archive(1)
        key = self.mirror.archive_key(entry)
        self.bucket.objects[key] = b'x' * entry['size']
        with self.assertRaisesRegex(ValueError, 'size or SHA-256'):
            self.mirror.publish(archive, entry, self.directory)
        archive.write_bytes(b'wrong Release bytes')
        with self.assertRaisesRegex(ValueError, 'differs from the published Release'):
            self.mirror.publish(archive, entry, self.directory)
        self.assertNotIn('current.json', self.bucket.objects)


if __name__ == '__main__':
    unittest.main()
