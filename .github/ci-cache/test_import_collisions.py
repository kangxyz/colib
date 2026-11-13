"""The optional diagnostic collects all outcomes without hiding failures."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location('collisions', Path(__file__).with_name('check_import_collisions.py'))
collisions = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(collisions)


class CollisionTests(unittest.TestCase):
    def test_continues_after_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            command = [sys.executable, '-c',
                       'import sys,pathlib;sys.exit(int("Bad" in pathlib.Path(sys.argv[1]).read_text()))']
            result = collisions.check_groups([
                {'modules': ['Good', 'Bad']}, {'modules': ['Good', 'Other']}],
                directory, directory, command, 5)
            self.assertEqual(result, 1)
            receipts = json.loads((Path(directory) / 'results.json').read_text())
            self.assertEqual([r['status'] for r in receipts], ['failed', 'passed'])

    def test_timeout_is_not_success(self):
        with tempfile.TemporaryDirectory() as directory:
            result = collisions.check_groups([{'modules': ['A', 'B']}], directory,
                directory, [sys.executable, '-c', 'import time;time.sleep(20)'], 0.1)
            self.assertEqual(result, 1)
            receipt = json.loads((Path(directory) / 'results.json').read_text())[0]
            self.assertEqual(receipt['status'], 'timeout')

    def test_rejects_invalid_module_names(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(ValueError):
                collisions.check_groups([{'modules': ['A', 'B\n#eval 1']}], directory,
                    directory, [sys.executable], 1)


if __name__ == '__main__':
    unittest.main()
