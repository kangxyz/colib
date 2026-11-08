#!/usr/bin/env python3
"""One authorized native provider cache run; not a Colib verification receipt."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
from types import SimpleNamespace

ROOT = Path.cwd()
OUT = Path(os.environ['RUNNER_TEMP']) / 'one-time-native'
ARCHIVE = OUT / 'stacks.tar.zst'
TARGETS = ROOT / '.github/ci-cache/one-time-native-targets.json'
EXPECTED_TARGETS = '8b4b52183d83f06398659a2e28954cdc8c7f6015b424ed81dcfe5073f657a901'
EXPECTED_ARCHIVE = '98d1c86fa18deb444dd622d1f7edf11cb3b72ffc913d909ffdb596682e10f41e'
EXPECTED_CONTEXT = '9845031f79bc7a61f7dbb6e27f1a12150a1eb35aae1effb4cf01a27c9a8cf840'
EXPECTED_GENERATION = '175e55ce8c71a8fef7671aea7ea9f78848a9e56e64f4f7953e331bf3a19b5a7f'
PART_BYTES = 384 * 1024**2
spec = importlib.util.spec_from_file_location('checkpoint', ROOT / '.github/ci-cache/checkpoint.py')
cp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cp)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def targets():
    require(cp.file_hash(TARGETS) == EXPECTED_TARGETS, 'target manifest changed')
    data = json.loads(TARGETS.read_text())
    require(len(data['modules']) == data['exact_modules'] == 308, 'unexpected module count')
    require(len(data['sink_targets']) == 6, 'unexpected target count')
    require(cp.contexts(ROOT)['stacks_context'] == EXPECTED_CONTEXT, 'checkout context changed')
    return data


def inspect(seed=False):
    data = targets()
    if seed:
        require(ARCHIVE.stat().st_size == 981184912, 'seed archive size changed')
        require(cp.file_hash(ARCHIVE) == EXPECTED_ARCHIVE, 'seed archive digest changed')
    args = SimpleNamespace(root=ROOT, layer='stacks', native_cache=Path(os.environ['LAKE_CACHE_DIR']))
    with cp.archive_stream(ARCHIVE, False) as stream, tarfile.open(fileobj=stream, mode='r|') as tar:
        members = iter(tar)
        header = next(members, None)
        require(header and header.name == 'checkpoint.json' and header.isreg()
                and header.size <= 256 * 1024**2, 'invalid manifest header')
        metadata = json.loads(tar.extractfile(header).read())
        entries = cp.validate_metadata(metadata, args)
        if seed:
            require(metadata['generation'] == EXPECTED_GENERATION, 'seed generation changed')
        # Read and save the manifest before any compiler/toolchain setup.
        (OUT / 'checkpoint.json').write_text(json.dumps(metadata, indent=2) + '\n')
        for entry in entries:
            member = next(members, None)
            require(member and member.isreg() and member.name == 'payload/' + entry['area'] + '/' + entry['path']
                    and member.size == entry['size'], 'invalid payload member')
            require(hashlib.file_digest(tar.extractfile(member), 'sha256').hexdigest() == entry['sha256'],
                    'payload digest mismatch')
        require(next(members, None) is None, 'unexpected payload member')
    available = {e['path'] for e in entries if e['area'] == 'workspace' and e['size'] > 0}
    suffixes = ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir', '.trace')
    missing = []
    for item in data['modules']:
        prefix = '.lake/packages/Stacks/.lake/build/lib/lean/' + item['module'].replace('.', '/')
        absent = [suffix for suffix in suffixes if prefix + suffix not in available]
        if absent:
            missing.append({'module': item['module'], 'missing': absent})
    report = {'covered': not missing, 'exact_modules': 308, 'missing': missing,
              'archive_sha256': cp.file_hash(ARCHIVE), 'generation': metadata['generation'],
              'context': metadata['context'], 'seed': seed,
              'note': 'Provider checkpoint coverage, not Colib proof or full CI verification.'}
    (OUT / 'coverage.json').write_text(json.dumps(report, indent=2) + '\n')
    if seed:
        shutil.copyfile(OUT / 'coverage.json', OUT / 'seed-coverage.json')
        with open(os.environ['GITHUB_OUTPUT'], 'a') as output:
            output.write(f"covered={str(not missing).lower()}\n")
    return report


def sources():
    data = targets()
    package = ROOT / '.lake/packages/Stacks'
    actual = subprocess.check_output(['git', '-C', str(package), 'rev-parse', 'HEAD'], text=True).strip()
    require(actual == data['native_pin'], 'materialized Stacks pin changed')
    for item in data['modules']:
        path = package / (item['module'].replace('.', '/') + '.lean')
        require(cp.file_hash(path) == item['sha256'], 'native source changed: ' + item['module'])
    (OUT / 'targets.txt').write_text('\n'.join('+' + name for name in data['sink_targets']) + '\n')


def split():
    report = inspect()
    ready = os.environ['NATIVE_READY_OUTCOME']
    built = os.environ['NATIVE_BUILD_OUTCOME']
    require(ready == 'success' or built == 'success', 'no native validity evidence')
    (OUT / 'native-validation.json').write_text(json.dumps({
        'no_build_rehash_outcome': ready, 'targeted_build_outcome': built,
        'targets': targets()['sink_targets'], 'proof_replay': False,
        'colib_verification': False}, indent=2) + '\n')
    require(report['covered'], 'requested native closure still incomplete')
    count = (ARCHIVE.stat().st_size + PART_BYTES - 1) // PART_BYTES
    require(1 <= count <= 8, 'archive exceeds bounded eight-part export')
    parts = []
    with ARCHIVE.open('rb') as source:
        for index in range(count):
            path = OUT / f'stacks.tar.zst.part-{index:02d}'
            with path.open('wb') as output:
                remaining = PART_BYTES
                while remaining and (chunk := source.read(min(remaining, 1024**2))):
                    output.write(chunk)
                    remaining -= len(chunk)
            parts.append({'name': path.name, 'bytes': path.stat().st_size, 'sha256': cp.file_hash(path)})
    (OUT / 'parts.json').write_text(json.dumps({'archive': 'stacks.tar.zst',
        'archive_bytes': ARCHIVE.stat().st_size, 'archive_sha256': report['archive_sha256'],
        'parts': parts, 'run_id': os.environ['GITHUB_RUN_ID'], 'commit': os.environ['GITHUB_SHA']}, indent=2) + '\n')
    shutil.copyfile(TARGETS, OUT / 'targets.json')
    with open(os.environ['GITHUB_OUTPUT'], 'a') as output:
        output.write(f'parts={count}\n')


if __name__ == '__main__':
    OUT.mkdir(parents=True, exist_ok=True)
    {'inspect': lambda: inspect(seed=True), 'sources': sources, 'split': split}[sys.argv[1]]()
