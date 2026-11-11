#!/usr/bin/env python3
"""Reuse a verified Stacks checkpoint; fall back only to the known exact baseline."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess

root = Path.cwd()
spec = importlib.util.spec_from_file_location('checkpoint', root / '.github/ci-cache/checkpoint.py')
checkpoint = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checkpoint)
plan = json.loads((root / '.github/strict-a1-cache/plan.json').read_text())
archive = root / '.lake/ci-checkpoints/stacks.tar.zst'
args = argparse.Namespace(root=root, layer='stacks', native_cache=Path(os.environ['LAKE_CACHE_DIR']).absolute(), metadata=None, github_output=None, input=archive)


def covered():
    for item in plan['cached_entries']:
        path = root / item['path']
        if not path.is_file() or path.is_symlink() or path.stat().st_size != item['size'] or checkpoint.file_hash(path) != item['sha256']:
            return False
    return True


checkpoint.supported(root, materialized=True)
if archive.is_file():
    checkpoint.restore(args)
if covered():
    print('All 306 exact baseline modules are present from the restored checkpoint.')
else:
    # This official asset identity was previously verified for the pinned plan.
    asset = 'https://api.github.com/repos/kangxyz/colib/releases/assets/733969670'
    archive.parent.mkdir(parents=True, exist_ok=True)
    with archive.open('wb') as stream:
        subprocess.run(['gh', 'api', asset, '-H', 'Accept: application/octet-stream'], stdout=stream, check=True)
    if archive.stat().st_size != 1586654451 or checkpoint.file_hash(archive) != '23436ff5612fb91f32ce13916df8076e8bc3af302d2024ab4600801d87aa817d':
        raise SystemExit('Pinned baseline archive size/SHA mismatch')
    checkpoint.restore(args)
    if not covered():
        raise SystemExit('Pinned baseline does not provide the exact 306 module products')
    print('Restored exact verified baseline asset 733969670; no new dependency compiled.')
