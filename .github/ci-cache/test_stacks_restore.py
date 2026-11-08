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

    def restore(self, *, prefix_fails=False):
        downloads = []

        def download(asset, output, *, prefix=False):
            downloads.append(prefix)
            if prefix and prefix_fails:
                output.write_bytes(b'partial zstd')
            else:
                shutil.copyfile(self.published, output)

        with patch.object(restore_stacks, 'download', side_effect=download), redirect_stdout(io.StringIO()) as log:
            restore_stacks.restore_stacks(self.args, self.warm,
                                         {'name': 'published.tar.zst', 'size': self.published.stat().st_size})
        return downloads, log.getvalue().count('"restored": true')

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
