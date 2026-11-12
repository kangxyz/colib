"""Regression tests for full and partial Stacks cache recovery."""
import argparse
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import checkpoint
from filter_lake_log import filter_log
import restore_stacks
from stacks_r2 import R2Cache


@unittest.skipUnless(shutil.which('zstd'), 'checkpoint compression needs zstd')
class StacksRestoreTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.base = Path(directory.name)
        self.root = self.base / 'root'
        self.build = self.root / '.lake/packages/Stacks/.lake/build/lib/lean'
        self.build.mkdir(parents=True)
        (self.root / 'lean-toolchain').write_text(checkpoint.SUPPORTED_TOOLCHAIN + '\n')
        (self.root / 'lakefile.toml').write_text('name = "Root"\n')
        (self.root / 'lake-manifest.json').write_text(json.dumps({'packages': [
            {'name': 'Stacks', 'type': 'git', 'rev': 'pin', 'url': 'https://example/Stacks'}]}))
        self.args = argparse.Namespace(root=self.root, layer='stacks', native_cache=self.base / 'native',
                                       metadata=None, github_output=None, production_root=[])
        self.shared = self.build / 'Shared.olean'
        self.missing = self.build / 'Missing.olean'
        self.shared.write_text('baseline shared output')
        self.missing.write_text('baseline missing output')
        self.published = self.base / 'published.tar.zst'
        self.warm = self.base / 'warm.tar.zst'
        self.pack(self.published)

    def pack(self, archive):
        self.args.output = archive
        with redirect_stdout(io.StringIO()):
            checkpoint.pack(self.args)

    def restore(self, *, prefix_fails=False, r2=None):
        downloads = []

        def download(asset, output, *, prefix=False):
            downloads.append(prefix)
            if prefix and prefix_fails:
                output.write_bytes(b'partial zstd')
            else:
                shutil.copyfile(self.published, output)

        asset = {'name': 'published.tar.zst', 'size': self.published.stat().st_size}
        with (patch.object(restore_stacks, 'published_asset', return_value=asset),
              patch.object(restore_stacks, 'download', side_effect=download),
              redirect_stdout(io.StringIO()) as log):
            restore_stacks.restore_stacks(self.args, self.warm, r2)
        return downloads, log.getvalue().count('"restored": true')

    def r2_baseline(self):
        manifest = restore_stacks.manifest(self.published, self.args)
        r2 = R2Cache('https://example', 'stacks', 'test', 'test', 'a' * 40, manifest['context'])
        index = {'schema': 1, 'revision': r2.revision, 'context': r2.context,
                 'generation': manifest['generation'], 'size': self.published.stat().st_size,
                 'sha256': checkpoint.file_hash(self.published)}
        return r2, index

    def test_same_generation_with_different_archive_bytes_is_restored_once(self):
        os.utime(self.shared, ns=(1_000_000, 1_000_000))
        self.pack(self.warm)
        self.assertNotEqual(self.published.read_bytes(), self.warm.read_bytes())
        self.shared.unlink()
        self.missing.unlink()
        self.assertEqual(self.restore(), ([True], 1))
        self.assertEqual(self.missing.read_text(), 'baseline missing output')

    def test_newer_partial_cache_overlays_the_baseline(self):
        self.missing.unlink()
        self.shared.write_text('newer shared output')
        self.pack(self.warm)
        self.shared.unlink()
        self.assertEqual(self.restore(), ([True, False], 2))
        self.assertEqual(self.shared.read_text(), 'newer shared output')
        self.assertEqual(self.missing.read_text(), 'baseline missing output')

    def test_superset_still_restores_once_with_a_failed_preview(self):
        extra = self.build / 'Extra.olean'
        extra.write_text('additional warm output')
        self.pack(self.warm)
        extra.unlink()
        self.assertEqual(self.restore(prefix_fails=True), ([True, False], 1))
        self.assertEqual(extra.read_text(), 'additional warm output')

    def test_invalid_warm_payload_falls_back_to_full_baseline(self):
        data = subprocess.check_output(['zstd', '-dc', self.published])
        data = data.replace(b'baseline shared output', b'corrupt! shared output')
        with self.warm.open('wb') as output:
            subprocess.run(['zstd', '-qc'], input=data, stdout=output, check=True)
        self.shared.unlink()
        self.missing.unlink()
        self.assertEqual(self.restore(), ([True, False], 1))
        self.assertEqual(self.warm.read_bytes(), self.published.read_bytes())
        self.assertEqual(self.shared.read_text(), 'baseline shared output')

    def test_r2_generation_hit_only_downloads_the_index(self):
        r2, index = self.r2_baseline()
        shutil.copyfile(self.published, self.warm)
        self.shared.unlink()
        self.missing.unlink()

        def request(method, key, output, **options):
            self.assertEqual((method, key), ('GET', 'current.json'))
            output.write_text(json.dumps(index))
            return 200, '"a"'

        with (patch.object(r2, 'request', side_effect=request),
              patch.object(restore_stacks, 'published_asset', side_effect=AssertionError('unexpected fallback')),
              redirect_stdout(io.StringIO())):
            restore_stacks.restore_stacks(self.args, self.warm, r2)
        self.assertEqual(self.missing.read_text(), 'baseline missing output')

    def test_r2_bad_digest_falls_back_without_losing_partial_progress(self):
        r2, index = self.r2_baseline()
        self.shared.write_text('newer shared output')
        self.missing.unlink()
        self.pack(self.warm)
        self.shared.unlink()

        def request(method, key, output, **options):
            if key == 'current.json':
                output.write_text(json.dumps(index))
                return 200, '"a"'
            data = self.published.read_bytes()
            if options['headers']:
                output.write_bytes(data)
                return 206, '"b"'
            output.write_bytes(data[:-1] + bytes([data[-1] ^ 1]))
            return 200, '"b"'

        with patch.object(r2, 'request', side_effect=request) as remote:
            self.assertEqual(self.restore(r2=r2), ([True, False], 2))
        self.assertEqual(remote.call_count, 3)
        self.assertEqual(self.shared.read_text(), 'newer shared output')
        self.assertEqual(self.missing.read_text(), 'baseline missing output')

    def test_r2_publish_rechecks_coverage_after_a_pointer_conflict(self):
        r2, index = self.r2_baseline()
        (self.build / 'Extra.olean').write_text('additional output')
        self.pack(self.warm)
        conditions = []
        archive_uploads = []

        def request(method, key, output, **options):
            if method == 'GET' and key == 'current.json':
                if not conditions:
                    return 404, ''
                output.write_text(json.dumps(index))
                return 200, '"a"'
            if method == 'GET':
                self.assertEqual(key, r2.archive_key(index))
                shutil.copyfile(self.published, output)
                return 206, '"b"'
            if key != 'current.json':
                archive_uploads.append(key)
                return 200, '"c"'
            conditions.append(options['headers'][0])
            pointer = json.loads(options['upload'].read_text())
            self.assertEqual(r2.archive_key(pointer), archive_uploads[0])
            return (412, '') if len(conditions) == 1 else (200, '"d"')

        with patch.object(r2, 'request', side_effect=request), redirect_stdout(io.StringIO()):
            restore_stacks.publish_r2(self.args, self.warm, r2)
        self.assertEqual(conditions, ['If-None-Match: *', 'If-Match: "a"'])
        self.assertEqual(len(archive_uploads), 1)

    def test_r2_publish_reuses_same_generation_uploaded_with_different_bytes(self):
        r2, existing = self.r2_baseline()
        os.utime(self.shared, ns=(1_000_000, 1_000_000))
        self.pack(self.warm)
        self.assertNotEqual(checkpoint.file_hash(self.warm), existing['sha256'])
        pointers = []

        def request(method, key, output, **options):
            if key == 'current.json':
                if method == 'GET':
                    return 404, ''
                pointers.append(json.loads(options['upload'].read_text()))
                return 200, '"c"'
            self.assertEqual(key, r2.archive_key(existing))
            if method == 'PUT':
                self.assertEqual(options['headers'][0], 'If-None-Match: *')
                return 412, ''
            self.assertEqual(method, 'HEAD')
            return 200, f"{existing['size']}\n{existing['sha256']}"

        with patch.object(r2, 'request', side_effect=request), redirect_stdout(io.StringIO()):
            restore_stacks.publish_r2(self.args, self.warm, r2)
        self.assertEqual(pointers, [existing])

    def test_github_release_skips_existing_legacy_generation(self):
        os.utime(self.shared, ns=(1_000_000, 1_000_000))
        self.pack(self.warm)
        legacy = {'id': 1, 'name': 'stacks-checkpoint-123-1.tar.zst', 'state': 'uploaded',
                  'size': self.published.stat().st_size, 'created_at': '2026-11-12T00:00:00Z',
                  'digest': 'sha256:' + checkpoint.file_hash(self.published)}
        self.assertNotEqual('sha256:' + checkpoint.file_hash(self.warm), legacy['digest'])

        def download(asset, output, *, prefix=False):
            self.assertEqual(asset, legacy)
            self.assertTrue(prefix)
            shutil.copyfile(self.published, output)

        with (patch.object(restore_stacks, 'github_release', return_value={'assets': [legacy]}),
              patch.object(restore_stacks, 'download', side_effect=download) as read,
              patch.object(restore_stacks.subprocess, 'run', side_effect=AssertionError('unexpected upload')),
              redirect_stdout(io.StringIO())):
            restore_stacks.publish_release(self.args, self.warm, 'a' * 40, 'b' * 64)
        self.assertEqual(read.call_count, 1)

    def test_github_release_upload_race_reuses_winning_asset(self):
        generation = restore_stacks.manifest(self.published, self.args)['generation']
        asset = {'name': f'stacks-checkpoint-{generation}.tar.zst', 'state': 'uploaded',
                 'size': self.published.stat().st_size}
        releases = [{'assets': []}, {'assets': [asset]}]
        rejected = subprocess.CompletedProcess([], 1, '', 'HTTP 422 already_exists')
        with (patch.object(restore_stacks, 'github_release', side_effect=releases),
              patch.object(restore_stacks.subprocess, 'run', return_value=rejected) as upload,
              patch.dict(os.environ, GITHUB_REPOSITORY='test/repo', GITHUB_SHA='a' * 40),
              redirect_stdout(io.StringIO())):
            restore_stacks.publish_release(self.args, self.published, 'a' * 40, 'b' * 64)
        command = upload.call_args.args[0]
        self.assertEqual(command[:3], ['gh', 'release', 'upload'])
        self.assertEqual(Path(command[4]).name, asset['name'])
        self.assertTrue(self.published.is_file())


class LakeLogTests(unittest.TestCase):
    def test_keeps_replay_status_non_stacks_warnings_and_all_failures(self):
        output = io.StringIO()
        filter_log(io.StringIO(
            '✔ [0/7] Ran job computation\n'
            '⚠ [1/7] Replayed StacksCore.Foo\n'
            'warning: StacksCore/Foo.lean:1:0: a warning\n'
            '  continuation\n'
            'info: successful Stacks output\n'
            '⚠ [2/7] Replayed Mathlib.Foo\n'
            'warning: preserve this\n'
            '✔ [3/7] Replayed Colib.Foo\n'
            '✔ [4/7] Built StacksFrontier.Bar\n'
            'error: build failed\n'
            '✖ [5/7] Building StacksFrontier.Broken\n'
            'warning: preserve context of failure\n'
            'error: preserve compiler error\n'
            'Some required targets logged failures:\n'
            '- StacksFrontier.Broken\n'), output)
        self.assertEqual(output.getvalue(),
                         '✔ [1/7] Replayed StacksCore.Foo\n'
                         '⚠ [2/7] Replayed Mathlib.Foo\n'
                         'warning: preserve this\n'
                         '✔ [3/7] Replayed Colib.Foo\n'
                         '✔ [4/7] Built StacksFrontier.Bar\n'
                         'error: build failed\n'
                         '✖ [5/7] Building StacksFrontier.Broken\n'
                         'warning: preserve context of failure\n'
                         'error: preserve compiler error\n'
                         'Some required targets logged failures:\n'
                         '- StacksFrontier.Broken\n')
