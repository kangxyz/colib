"""Export bounded, integrity-checked native modules from a successful CI build."""
import hashlib
import json
import os
from pathlib import Path
import tarfile

root = Path('.')
package = root / '.lake/packages/Stacks'
plan = json.loads((root / '.github/ci-cache/p1-geometry-cache-plan.json').read_text())
out = Path(os.environ['RUNNER_TEMP']) / 'p1-geometry-dependencies'
out.mkdir(exist_ok=True)
limit = 160 * 1024**2
groups = [[]]
size = 0
for module in plan['modules']:
    stem = Path(module.replace('.', '/'))
    files = sorted(p for base in ('lib/lean', 'ir')
                   for p in (package / '.lake/build' / base / stem.parent).glob(stem.name + '.*')
                   if p.is_file() and not p.is_symlink() and not p.name.endswith('.setup.json'))
    assert any(str(p).endswith('.olean') for p in files), module
    assert any(str(p).endswith('.trace') for p in files), module
    module_size = sum(p.stat().st_size for p in files)
    assert module_size < limit, (module, module_size)
    if size + module_size > limit:
        groups.append([])
        size = 0
    groups[-1].append((module, files))
    size += module_size
assert 0 < len(groups) <= 16
base = {
    'producer': os.environ['GITHUB_SHA'],
    'run_id': os.environ['GITHUB_RUN_ID'],
    'lean_toolchain': (root / 'lean-toolchain').read_text().strip(),
    'packages': json.loads((root / 'lake-manifest.json').read_text())['packages'],
    'targets': plan['targets']
}
index = dict(base, parts=[])
for i, group in enumerate(groups):
    directory = out / f'part-{i:02d}'
    directory.mkdir(exist_ok=True)
    files = [p for _, fs in group for p in fs]
    manifest = dict(base,
        source_sha256={m.replace('.', '/'): hashlib.sha256(
            (package / Path(m.replace('.', '/')).with_suffix('.lean')).read_bytes()).hexdigest()
            for m, _ in group},
        files=[{'path': str(p.relative_to(package)), 'size': p.stat().st_size,
                'sha256': hashlib.sha256(p.read_bytes()).hexdigest()} for p in files])
    (directory / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    archive_path = directory / 'p1-dependency.tar'
    with tarfile.open(archive_path, 'w') as archive:
        for p in files:
            archive.add(p, arcname=str(p.relative_to(package)), recursive=False)
    assert archive_path.stat().st_size < 192 * 1024**2
    index['parts'].append({'artifact': f'p1-geometry-{i:02d}',
        'modules': [m for m, _ in group],
        'tar_sha256': hashlib.sha256(archive_path.read_bytes()).hexdigest(),
        'tar_bytes': archive_path.stat().st_size})
index_dir = out / 'index'
index_dir.mkdir(exist_ok=True)
(index_dir / 'index.json').write_text(json.dumps(index, indent=2) + '\n')
with open(os.environ['GITHUB_OUTPUT'], 'a') as stream:
    stream.write(f'parts={len(groups)}\n')
print(json.dumps({'modules': len(plan['modules']), 'parts': len(groups)}))
