#!/usr/bin/env python3
"""CI-only scoped working-build checkpoints; native Lake remains the validity gate.

Archives contain regular generated files and an integrity/coverage manifest. They
are compilation accelerators from trusted producers, never successful-check
receipts. No source checkout, Git state or whole Lake content store is copied.
"""
import argparse
from contextlib import contextmanager
import errno
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile

SCHEMA = 2
LAYERS = ('root', 'dependencies', 'stacks', 'tools')
SUPPORTED_TOOLCHAIN = 'leanprover/lean4:v4.35.0'
SUPPORTED_TOOLCHAINS = (SUPPORTED_TOOLCHAIN, 'leanprover/lean4:v4.34.1', 'leanprover/lean4:v4.34.0-rc2')
AUDITOR_PIN = '46024e005996495c65ef609368e11ab39c4222e3'
STAGING_RESERVE = 2 * 1024**3
# Explicit current public Lean configurations with default native build roots.
# These are source identities, not a parser for arbitrary executable lakefiles.
# Primary sources: leanprover-community/{mathlib4,ProofWidgets4}/blob/<rev>/lakefile.lean.
LEAN_CONFIGS = {
    ('mathlib', '56a005855ea17e0b0958f73ec801ae140b0a1679'):
        ('https://github.com/leanprover-community/mathlib4',
         '6083173bc380adea0cfd26f9a7813637ae0fd2c38c6a0d4536626e82a9538ef6'),
    ('proofwidgets', 'df72b022e558978a1c50264cfc4d7fec86fa8e04'):
        ('https://github.com/leanprover-community/ProofWidgets4',
         '0a319fffbf511dab4c3307dc105f8e8fdb4f6160020995cef5f442061cc0abca'),
    ('mathlib', '16edf57de7933555826307a3d81b4391a3657a09'):
        ('https://github.com/leanprover-community/mathlib4',
         '525c4828509e3d3c5642a7a2e71f6825cc51206d3d6f159dc95c9f1def95436a'),
    ('proofwidgets', 'a8acbfd87375ff4abe14ce09db5b7664d383bc7f'):
        ('https://github.com/leanprover-community/ProofWidgets4',
         '0a319fffbf511dab4c3307dc105f8e8fdb4f6160020995cef5f442061cc0abca'),
    ('mathlib', 'd13f23b723b8a846827a245b89c10fc7d3f11612'):
        ('https://github.com/leanprover-community/mathlib4',
         '274e720ccc7dbabeb9fbf362290dc7e5ed2c5175fbade0ef20cc19b1331affaf'),
    ('proofwidgets', '106ff4fafc74ef4ac99d81dbf3ab399118f497a5'):
        ('https://github.com/leanprover-community/ProofWidgets4',
         '0a319fffbf511dab4c3307dc105f8e8fdb4f6160020995cef5f442061cc0abca'),
}


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def file_hash(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def relative(value):
    if not isinstance(value, str) or not value or '\\' in value:
        raise ValueError('invalid relative checkpoint path')
    path = PurePosixPath(value)
    if path.is_absolute() or any(p in ('', '.', '..') for p in value.split('/')):
        raise ValueError('absolute or traversing checkpoint path: ' + value)
    return path


def contained(base, name, checked_parents=None):
    """Check lexical containment and every leaf; memo parents only in a quiescent pass."""
    parts = relative(name).parts
    current = base
    for component in (None, *parts[:-1]):
        if component is not None:
            current /= component
        if checked_parents is None or current not in checked_parents:
            if current.is_symlink():
                raise ValueError('symlink in checkpoint path: ' + str(current))
            if checked_parents is not None:
                checked_parents.add(current)
    path = current / parts[-1]
    # Never memoize leaves: a prior regular file can be an inherited hardlink or
    # a newly introduced symlink. Atomic replacement still breaks hardlinks.
    if path.is_symlink():
        raise ValueError('symlink in checkpoint path: ' + str(path))
    return path


def configuration(root):
    import tomllib
    file = root / 'lakefile.toml'
    return tomllib.loads(file.read_text()) if file.is_file() else {}


def default_build_layout(config):
    for key, default in (('buildDir', '.lake/build'), ('leanLibDir', 'lib/lean'),
                         ('nativeLibDir', 'lib'), ('binDir', 'bin'), ('irDir', 'ir')):
        if config.get(key, default) != default:
            raise ValueError('custom generated build directory is unsupported: ' + key)


def supported(root, materialized=False):
    """Admit only the static resolution boundary this CI helper implements.

    This runs before dependency checkouts exist. Lake overrides/custom layouts
    remain on legacy transport rather than being guessed after an expensive build.
    Commands repeat this guard because an old cache may introduce an override.
    """
    root = root.absolute()
    for name in ('lakefile.toml', 'lakefile.lean', 'lake-manifest.json',
                 'lean-toolchain', '.lake/package-overrides.json'):
        contained(root, name)
    if (root / 'lean-toolchain').read_text().strip() not in SUPPORTED_TOOLCHAINS:
        raise ValueError('unsupported layered checkpoint toolchain; use legacy transport')
    if (root / 'lakefile.lean').exists() or not (root / 'lakefile.toml').is_file():
        raise ValueError('layered checkpoints require an unambiguous root lakefile.toml')
    if (root / '.lake/package-overrides.json').exists():
        raise ValueError('package-overrides.json is outside layered checkpoint resolution')
    config = configuration(root)
    default_build_layout(config)
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    if config.get('packagesDir', '.lake/packages') != '.lake/packages' or \
            manifest.get('packagesDir', '.lake/packages') != '.lake/packages' or \
            manifest.get('lakeDir', '.lake') != '.lake':
        raise ValueError('layered checkpoints require the standard .lake/packages layout')
    packages = manifest.get('packages')
    if not isinstance(packages, list):
        raise ValueError('missing resolved package list')
    names, directories = set(), set()
    for item in packages:
        if not isinstance(item, dict) or not isinstance(item.get('name'), str) or \
                not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_-]*', item['name']):
            raise ValueError('unsupported manifest package name')
        if item['name'] in names:
            raise ValueError('duplicate manifest package name')
        names.add(item['name'])
        if item.get('subDir') is not None or item.get('configFile', 'lakefile.toml') not in \
                ('lakefile.toml', 'lakefile.lean') or \
                item.get('manifestFile', 'lake-manifest.json') != 'lake-manifest.json':
            raise ValueError('custom dependency configuration/subdirectory is unsupported')
        if item.get('type') == 'git':
            name = '.lake/packages/' + item['name']
        elif item.get('type') == 'path' and isinstance(item.get('dir'), str):
            value = Path(item['dir'])
            if value.is_absolute():
                try:
                    name = value.relative_to(root).as_posix()
                except ValueError as error:
                    raise ValueError('external path dependency is not checkpointable') from error
            else:
                name = str(relative(item['dir']))
        else:
            raise ValueError('unsupported resolved dependency type')
        path = contained(root, name)
        config_name = item.get('configFile', 'lakefile.toml')
        config_path = path / config_name
        if config_path.is_symlink():
            raise ValueError('resolved dependency configuration is not regular')
        if config_name == 'lakefile.lean':
            known = LEAN_CONFIGS.get((item['name'], item.get('rev')))
            url = item.get('url', '').removesuffix('.git')
            if item.get('type') != 'git' or not known or url != known[0]:
                raise ValueError('arbitrary executable dependency configuration is unsupported')
            if config_path.is_file() and file_hash(config_path) != known[1]:
                raise ValueError('known dependency configuration bytes changed')
        elif (path / 'lakefile.lean').exists():
            raise ValueError('competing dependency Lean configuration is unsupported')
        elif config_path.is_file():
            import tomllib
            default_build_layout(tomllib.loads(config_path.read_text()))
        if materialized and not config_path.is_file():
            raise ValueError('resolved dependency configuration is not materialized/regular')
        if materialized and item['name'] == 'Stacks' and item.get('type') == 'git':
            revision = subprocess.check_output(
                ['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
            dirty = subprocess.check_output(
                ['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no'],
                text=True).strip()
            if revision != item['rev'] or dirty:
                raise ValueError('Stacks source differs from the pinned clean checkout')
        # The root package, Git metadata, and nested aliases do not identify
        # independent resolved package scopes. Hyphenated leaf names are valid.
        if path == root or '.git' in path.relative_to(root).parts:
            raise ValueError('invalid resolved dependency directory')
        if any(path == previous or path.is_relative_to(previous) or previous.is_relative_to(path)
               for previous in directories):
            raise ValueError('duplicate or overlapping dependency directory')
        directories.add(path)
    return True


def dependencies(root):
    """Only resolved, repository-contained package directories are admitted."""
    supported(root)
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    packages = []
    directory = manifest.get('packagesDir', '.lake/packages')
    relative(directory)
    for item in manifest['packages']:
        if item['type'] == 'git':
            name = str(relative(directory) / relative(item['name']))
            if item.get('subDir'):
                name += '/' + str(relative(item['subDir']))
        elif item['type'] == 'path':
            value = Path(item['dir'])
            if value.is_absolute():
                try:
                    name = value.relative_to(root).as_posix()
                except ValueError as error:
                    raise ValueError('external path dependency is not checkpointable') from error
            else:
                name = str(relative(item['dir']))
        else:
            raise ValueError('unsupported resolved dependency type')
        path = contained(root, name)
        if path == root or path in packages:
            raise ValueError('duplicate/root dependency directory')
        packages.append(path)
    return sorted(packages)


def contexts(root):
    supported(root)
    inputs = {}
    for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'lakefile.lean',
                 '.lake/package-overrides.json'):
        path = contained(root, name)
        inputs[name] = file_hash(path) if path.is_file() else None
    # Runtime identity plus resolved pins/configuration, not changing proof sources.
    value = {'schema': SCHEMA, 'system': platform.system(), 'machine': platform.machine(),
             'inputs': inputs}
    common = digest(value)
    tools = {}
    for directory in (root / '.github/lint', root / 'scripts/lean_tools/_lint'):
        if directory.is_dir():
            for path in sorted(directory.iterdir()):
                if path.is_file() and not path.is_symlink():
                    tools[path.relative_to(root).as_posix()] = file_hash(path)
    dependency_context = digest({'base': common, 'policy': 'official-mathlib-v1'})
    return {'root_context': common, 'dependencies_context': dependency_context, 'stacks_context': common,
            'tools_context': digest({'base': dependency_context, 'tools': tools, 'auditor': AUDITOR_PIN})}


def tree_entries(path):
    def visit(directory, in_ir):
        with os.scandir(directory) as stream:
            children = sorted(stream, key=lambda child: child.name)
        directories = []
        for child in children:
            value = child.stat(follow_symlinks=False)
            if stat.S_ISDIR(value.st_mode):
                directories.append(child.path)
            elif stat.S_ISLNK(value.st_mode):
                raise ValueError('symlinked generated output: ' + child.path)
            elif not stat.S_ISREG(value.st_mode):
                raise ValueError('nonregular generated output: ' + child.path)
            # Lake's compiler setup input is neither an output nor a readiness input.
            elif not (in_ir and child.name.endswith('.setup.json')):
                yield Path(child.path), value
        for child in directories:
            yield from visit(child, in_ir or child.endswith('/.lake/build/ir'))

    try:
        value = path.lstat()
    except FileNotFoundError:
        return
    if stat.S_ISDIR(value.st_mode):
        yield from visit(path, '/.lake/build/ir/' in path.as_posix() + '/')
    elif stat.S_ISREG(value.st_mode):
        yield path, value
    else:
        raise ValueError('nonregular checkpoint scope: ' + str(path))


def tree(path):
    for entry, _ in tree_entries(path):
        yield entry


def allowed_scopes(root, layer, native):
    scopes = []
    if layer == 'root':
        scopes += [('workspace', root / '.lake/build'), ('workspace', root / '.lake/config')]
    if layer in ('dependencies', 'tools'):
        for package in dependencies(root):
            if package.name == 'Stacks':
                continue
            if package.name == 'mathlib':
                # The pinned official provider supplies production Mathlib outputs.
                # Only development tools belong in the project tools checkpoint.
                if layer == 'tools':
                    scopes += [('workspace', package / '.lake/config')]
                    for name in ('bin', 'ir/Cache', 'lib/lean/Cache', 'ir/scripts', 'lib/lean/scripts'):
                        scopes += [('workspace', package / '.lake/build' / name)]
                continue
            scopes += [('workspace', package / '.lake/build'), ('workspace', package / '.lake/config')]
    if layer == 'stacks':
        for package in dependencies(root):
            if package.name == 'Stacks':
                scopes += [('workspace', package / '.lake/build'), ('workspace', package / '.lake/config')]
    if layer == 'tools':
        private = root / '.lake/lint-runner'
        scopes += [('workspace', private / '.lake/build'), ('workspace', private / '.lake/config')]
        scopes += [('workspace', private / name) for name in
                   ('lakefile.toml', 'lean-toolchain', 'lake-manifest.json', 'BatchedLint.lean')]
        scopes += [('native', native / 'axiom-audit/.lake/build'),
                   ('native', native / 'axiom-audit/.lake/config')]
    return scopes


def stat_identity(value):
    return (value.st_dev, value.st_ino, value.st_mode, value.st_size,
            value.st_mtime_ns, value.st_ctime_ns)


def directory_identity(value):
    # Archive creation and ordinary reads can change directory times. Resolution
    # identity/type must stay fixed; a replaced directory/symlink is rejected.
    return value.st_dev, value.st_ino, stat.S_IFMT(value.st_mode)


def file_entry(path, area, name, before, previous):
    identity = stat_identity(before)
    saved = previous.get((area, name)) if previous is not None else None
    unchanged = saved is not None and saved[0] == identity
    value = {'area': area, 'path': name, 'size': before.st_size,
             'mode': stat.S_IMODE(before.st_mode) & 0o777,
             'mtime_ns': before.st_mtime_ns, 'sha256': saved[1] if unchanged else file_hash(path)}
    if not unchanged and identity != stat_identity(path.lstat()):
        raise ValueError('generated file changed during checkpoint scan: ' + name)
    return value, identity, unchanged


def record_parents(directory, base, directories):
    while directory not in directories:
        value = directory.lstat()
        if not stat.S_ISDIR(value.st_mode):
            raise ValueError('checkpoint directory is not regular: ' + str(directory))
        directories[directory] = directory_identity(value)
        if directory == base:
            break
        directory = directory.parent


def semantic(entry):
    return {k: v for k, v in entry.items() if k != 'mtime_ns'}


def snapshot(root, layer, native, guards, directories, previous):
    baseline = {}
    if layer == 'tools':
        saved = root / '.lake/ci-cache/dependencies.json'
        data = json.loads(saved.read_text())
        if data.get('context') != contexts(root)['dependencies_context'] or data.get('layer') != 'dependencies':
            raise ValueError('tools need the matching CURRENT dependency baseline manifest')
        baseline = {(e['area'], e['path']): semantic(e) for e in data['entries']}
    entries = {}
    reused_hashes = 0
    for area, directory in allowed_scopes(root, layer, native):
        base = root if area == 'workspace' else native
        contained(base, directory.relative_to(base).as_posix())
        for path, value_stat in tree_entries(directory):
            name = relative(path.relative_to(base).as_posix()).as_posix()
            entry, identity, unchanged = file_entry(path, area, name, value_stat, previous)
            key = (area, name)
            if layer == 'tools' and key in baseline and semantic(entry) == baseline[key]:
                continue
            guards[key] = identity
            record_parents(path.parent, base, directories)
            entries[key] = entry
            reused_hashes += unchanged
    return sorted(entries.values(), key=lambda e: (e['area'], e['path'])), reused_hashes


@contextmanager
def archive_stream(path, writing, *, header_only=False):
    """Stream zstd on Linux; no simultaneous expanded tar is required."""
    if path.name.endswith('.tar.zst'):
        if writing:
            with path.open('wb') as target:
                process = subprocess.Popen(['zstd', '-q', '-T2', '-1', '-c'],
                                           stdin=subprocess.PIPE, stdout=target)
                stream = process.stdin
                try:
                    yield stream
                finally:
                    stream.close()
                    code = process.wait()
                    if code:
                        raise ValueError('checkpoint zstd compression failed')
        else:
            process = subprocess.Popen(['zstd', '-q', '-d', '-c', str(path)], stdout=subprocess.PIPE,
                                       stderr=subprocess.DEVNULL if header_only else None)
            try:
                yield process.stdout
            except BaseException:
                process.stdout.close()
                process.wait()
                raise
            else:
                # tar ends before zstd's frame checksum. Drain the stream so
                # a corrupt or truncated compressed tail cannot pass validation.
                try:
                    if not header_only:
                        while process.stdout.read(1024 * 1024):
                            pass
                finally:
                    process.stdout.close()
                    code = process.wait()
                if code and not header_only:
                    raise ValueError('checkpoint zstd decompression failed')
    else:
        with path.open('wb' if writing else 'rb') as stream:
            yield stream


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(data, sort_keys=True) + '\n')
    os.replace(temporary, path)


def emit(data, output=None):
    print(json.dumps(data, sort_keys=True), flush=True)
    if output:
        with Path(output).open('a') as stream:
            for name, value in data.items():
                if isinstance(value, (str, int, bool)):
                    text = str(value).lower() if isinstance(value, bool) else str(value)
                    if '\n' in text or '\r' in text:
                        raise ValueError('multiline action output')
                    stream.write(f'{name}={text}\n')


class DigestingReader:
    """Hash exactly the data tarfile copies, without a separate body reread."""
    def __init__(self, source):
        self.source = source
        self.hasher = hashlib.sha256()
        self.size = 0

    def read(self, size=-1):
        data = self.source.read(size)
        self.hasher.update(data)
        self.size += len(data)
        return data


def check_directories(directories):
    for path, expected in directories.items():
        if directory_identity(path.lstat()) != expected:
            raise ValueError('generated directory changed during checkpoint copy: ' + str(path))


def local_checkpoint(args, context, state):
    # This receipt is created inside the current run on the same runner.
    try:
        receipt = json.loads(state.read_text())
        archive = args.output.lstat()
        if (receipt['schema'] != 1 or receipt['layer'] != args.layer or receipt['context'] != context
                or receipt['production_roots'] != args.production_root
                or not stat.S_ISREG(archive.st_mode)
                or receipt['archive'] != list(stat_identity(archive))):
            return None, None
        # ctime detects a write even when a tool restores the old mtime.
        previous = {(area, name): (tuple(identity), sha)
                    for area, name, identity, sha in receipt['files']}
        return receipt, previous
    except (OSError, ValueError, TypeError, KeyError):
        return None, None


def write_local_state(path, metadata, archive, identities):
    receipt = {name: metadata[name] for name in ('layer', 'context', 'generation')}
    receipt['production_roots'] = metadata.get('production_roots', [])
    receipt.update(schema=1, archive=stat_identity(archive.lstat()),
                   files=[[e['area'], e['path'], identities[(e['area'], e['path'])], e['sha256']]
                          for e in metadata['entries']])
    write_json(path, receipt)


def pack(args):
    root, native = args.root, args.native_cache
    layer = args.layer
    context = contexts(root)[layer + '_context']
    local_state = getattr(args, 'local_state', None)
    receipt, previous = local_checkpoint(args, context, local_state) if local_state is not None else (None, None)
    guards, directories = {}, {}
    entries, reused_hashes = snapshot(root, layer, native, guards, directories, previous)
    generation = digest([semantic(e) for e in entries])
    target = args.output
    if (receipt is not None and receipt.get('generation') == generation
            and receipt['archive'] == list(stat_identity(target.lstat()))):
        check_directories(directories)
        if list(stat_identity(target.lstat())) != receipt['archive']:
            raise ValueError('checkpoint archive changed during pack')
        emit({'generation': generation, 'context': context, 'changed': False,
              'bytes': target.stat().st_size, 'files': len(entries), 'archive': str(target),
              'reused_archive': True, 'reused_local_state': True,
              'reused_file_hashes': reused_hashes}, args.github_output)
        return

    metadata = {'schema': SCHEMA, 'layer': layer, 'context': context,
                'generation': generation, 'production_roots': args.production_root, 'entries': entries}
    restored = root / '.lake/ci-cache' / (layer + '.json')
    try:
        old = json.loads(restored.read_text())
    except (OSError, ValueError):
        old = {}
    baseline = receipt if receipt is not None else old
    changed = baseline.get('context') != context or baseline.get('generation') != generation
    target.parent.mkdir(parents=True, exist_ok=True)

    def record_local_state():
        if local_state is not None:
            write_local_state(local_state, metadata, target, guards)

    if (old.get('context') == context and old.get('generation') == generation
            and target.is_file() and old.get('archive_sha256') == file_hash(target)):
        # This exact archive was fully validated during restore. Ignore changed
        # mtimes in compatibility; identical content/modes need no recompression.
        retained = {k: v for k, v in old.items() if k != 'archive_sha256'}
        write_json(args.metadata or Path(str(target) + '.json'), retained)
        record_local_state()
        emit({'generation': generation, 'context': context, 'changed': False,
              'bytes': target.stat().st_size, 'files': len(entries), 'archive': str(target),
              'reused_archive': True, 'reused_file_hashes': reused_hashes}, args.github_output)
        return
    temporary = target.with_name('partial-' + target.name)
    try:
        check_directories(directories)
        with archive_stream(temporary, True) as stream, tarfile.open(fileobj=stream, mode='w|') as archive:
            content = (json.dumps(metadata, sort_keys=True) + '\n').encode()
            header = tarfile.TarInfo('checkpoint.json')
            header.size = len(content)
            header.mode = 0o644
            archive.addfile(header, io.BytesIO(content))
            for entry in entries:
                base = root if entry['area'] == 'workspace' else native
                # Paths were canonicalized and their directories guarded in the
                # initial scan. Copy checks are constant-time lstat/fstat guards.
                path = base / entry['path']
                expected = guards[(entry['area'], entry['path'])]
                if stat_identity(path.lstat()) != expected:
                    raise ValueError('generated output changed before archive copy')
                header = tarfile.TarInfo('payload/' + entry['area'] + '/' + entry['path'])
                header.size, header.mode = entry['size'], entry['mode']
                header.mtime = entry['mtime_ns'] / 1_000_000_000
                descriptor = os.open(path, os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0))
                with os.fdopen(descriptor, 'rb') as source:
                    if stat_identity(os.fstat(source.fileno())) != expected:
                        raise ValueError('generated output changed while opening for archive copy')
                    copied = DigestingReader(source)
                    archive.addfile(header, copied)
                    if copied.size != entry['size'] or copied.hasher.hexdigest() != entry['sha256']:
                        raise ValueError('copied checkpoint content differs from snapshot')
                    if stat_identity(os.fstat(source.fileno())) != expected:
                        raise ValueError('generated output changed during archive copy')
                if stat_identity(path.lstat()) != expected:
                    raise ValueError('generated output changed during archive copy')
        check_directories(directories)
        os.replace(temporary, target)
    finally:
        temporary.unlink(missing_ok=True)
    write_json(args.metadata or Path(str(target) + '.json'), metadata)
    record_local_state()
    emit({'generation': generation, 'context': context, 'changed': changed,
          'bytes': target.stat().st_size, 'files': len(entries), 'archive': str(target),
          'reused_file_hashes': reused_hashes}, args.github_output)


def validate_metadata(data, args, checked_parents=None, targets=None):
    if data.get('schema') != SCHEMA or data.get('layer') != args.layer:
        raise ValueError('unsupported checkpoint schema/layer')
    if data.get('context') != contexts(args.root)[args.layer + '_context']:
        raise ValueError('incompatible checkpoint context')
    entries = data.get('entries')
    if not isinstance(entries, list) or data.get('generation') != digest([semantic(e) for e in entries]):
        raise ValueError('invalid checkpoint generation')
    scopes = set(allowed_scopes(args.root, args.layer, args.native_cache))
    names = set()
    parents = {}
    prefixes = {}
    for area, path in scopes:
        base = args.root if area == 'workspace' else args.native_cache
        prefixes.setdefault(area, set()).add(path.relative_to(base).as_posix())
    for e in entries:
        if e.get('area') not in ('workspace', 'native') or type(e.get('size')) is not int or e['size'] < 0:
            raise ValueError('invalid checkpoint entry')
        if type(e.get('mode')) is not int or not 0 <= e['mode'] <= 0o777:
            raise ValueError('invalid checkpoint mode')
        if type(e.get('mtime_ns')) is not int or e['mtime_ns'] < 0 or \
                not re.fullmatch('[0-9a-f]{64}', str(e.get('sha256'))):
            raise ValueError('invalid checkpoint identity')
        key = (e['area'], e['path'])
        if key in names:
            raise ValueError('duplicate checkpoint entry')
        names.add(key)
        base = args.root if e['area'] == 'workspace' else args.native_cache
        name = e['path']
        parts = relative(name).parts
        parent_name = '/'.join(parts[:-1])
        parent_key = (e['area'], parent_name)
        area_scopes = prefixes.get(e['area'], set())
        if parent_key not in parents:
            parent = base if not parent_name else contained(base, parent_name, checked_parents)
            covered = any(parent_name == scope or parent_name.startswith(scope + '/') for scope in area_scopes)
            parents[parent_key] = parent, covered
        parent, covered = parents[parent_key]
        if not covered and name not in area_scopes:
            raise ValueError('checkpoint entry outside generated scopes')
        path = parent / parts[-1]
        try:
            mode = path.lstat().st_mode
        except FileNotFoundError:
            pass
        else:
            if not stat.S_ISREG(mode):
                raise ValueError('checkpoint output destination is not a regular file: ' + str(path))
        if targets is not None:
            targets.append(path)
    return entries


def read_metadata(archive, members):
    header = next(members, None)
    if header is None or header.name != 'checkpoint.json' or not header.isreg() or header.size > 256 * 1024**2:
        raise ValueError('missing/oversized checkpoint manifest')
    with archive.extractfile(header) as stream:
        return json.load(stream)


class UseTwoPassRestore(Exception):
    """The runner cannot keep a complete staged copy."""


def check_stage_capacity(directory, entries):
    usage = os.statvfs(directory)
    block = usage.f_frsize or usage.f_bsize
    required = sum(((e['size'] + block - 1) // block + 1) * block for e in entries)
    if (usage.f_bavail * block < required + STAGING_RESERVE
            or (usage.f_files and usage.f_favail < 2 * len(entries) + 1024)):
        raise UseTwoPassRestore('insufficient disk space or inodes for staging')


def staged_workspace(args, metadata):
    # Native-tool archives can span two filesystems. Keep those on the existing
    # two-pass path so installing a verified file never requires a cross-device copy.
    if any(e['area'] != 'workspace' for e in metadata['entries']):
        raise UseTwoPassRestore('checkpoint includes a separate native store')
    check_stage_capacity(args.root / '.lake', metadata['entries'])


def restore_pass(args, *, expected=None, apply=False, staging=None, identities=None):
    checked_parents = set()
    with archive_stream(args.input, False) as stream, tarfile.open(fileobj=stream, mode='r|') as archive:
        members = iter(archive)
        metadata = read_metadata(archive, members)
        targets = []
        entries = validate_metadata(metadata, args, checked_parents, targets)
        if expected is not None and metadata != expected:
            raise ValueError('archive manifest changed during restore')
        if staging is not None:
            staged_workspace(args, metadata)
        created_parents = set()
        for entry, target in zip(entries, targets):
            member = next(members, None)
            name = entry['path']
            if (member is None or not member.isreg() or member.size != entry['size']
                    or member.name != f"payload/{entry['area']}/{name}"):
                raise ValueError('missing, nonregular or unexpected checkpoint member')
            output = temporary = None
            try:
                if staging is not None:
                    # Scope, names and destination symlinks were checked above.
                    output_path = staging / name
                    if output_path.parent not in created_parents:
                        output_path.parent.mkdir(parents=True, exist_ok=True)
                        created_parents.add(output_path.parent)
                    output = output_path.open('xb')
                elif apply:
                    if target.parent not in created_parents:
                        target.parent.mkdir(parents=True, exist_ok=True)
                        created_parents.add(target.parent)
                    fd, tmp_name = tempfile.mkstemp(prefix='.checkpoint-', dir=target.parent)
                    temporary = output_path = Path(tmp_name)
                    output = os.fdopen(fd, 'wb')
                with archive.extractfile(member) as source:
                    hasher = hashlib.sha256()
                    while chunk := source.read(1024 * 1024):
                        hasher.update(chunk)
                        if output is not None:
                            output.write(chunk)
                if hasher.hexdigest() != entry['sha256']:
                    raise ValueError('checkpoint content hash mismatch')
                if output is not None:
                    output.close()
                    output = None
                    os.chmod(output_path, entry['mode'])
                    os.utime(output_path, ns=(entry['mtime_ns'], entry['mtime_ns']))
                if apply:
                    os.replace(temporary, target)
                    if identities is not None:
                        identities[(entry['area'], name)] = stat_identity(target.lstat())
            finally:
                if output is not None:
                    output.close()
                if temporary is not None:
                    temporary.unlink(missing_ok=True)
        if next(members, None) is not None:
            raise ValueError('unexpected extra checkpoint member')
    return metadata, targets


def install_staged(root, staging, entries, targets, identities):
    device = staging.stat().st_dev
    checked_parents = set()
    for parent in {target.parent for target in targets}:
        # A mounted generated directory must use the existing file-by-file path.
        contained(root, parent.relative_to(root).as_posix(), checked_parents)
        nearest = parent
        while not nearest.exists():
            nearest = nearest.parent
        if nearest.stat().st_dev != device:
            raise UseTwoPassRestore('generated outputs are on a separate filesystem')
    installed_parents = set()
    for entry, target in zip(entries, targets):
        if target.parent not in installed_parents:
            target.parent.mkdir(parents=True, exist_ok=True)
            installed_parents.add(target.parent)
        os.replace(staging / entry['path'], target)
        if identities is not None:
            # rename updates ctime. Keep the post-install identity of these exact bytes.
            identities[(entry['area'], entry['path'])] = stat_identity(target.lstat())


def restore(args, *, verify_only=False):
    """Check every generated member before installing any checkpoint output."""
    if verify_only:
        return restore_pass(args)[0]
    method = 'two-pass'
    metadata = None
    local_state = getattr(args, 'local_state', None)
    identities = {} if local_state is not None else None
    compressed = stat_identity(args.input.stat())
    destination = args.root / '.lake'
    if destination.is_symlink():
        raise ValueError('checkpoint staging requires a regular .lake directory')
    try:
        destination.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='ci-restore-', dir=destination) as directory:
            staging = Path(directory)
            staged, targets = restore_pass(args, staging=staging)
            if stat_identity(args.input.stat()) != compressed:
                raise ValueError('checkpoint archive changed during restore')
            install_staged(args.root, staging, staged['entries'], targets, identities)
            metadata = staged
            method = 'staged'
    except UseTwoPassRestore as error:
        print(f'Using two-pass checkpoint restore: {error}', file=sys.stderr)
    except OSError as error:
        if error.errno not in (errno.ENOSPC, errno.EDQUOT, errno.EXDEV):
            raise
        print(f'Using two-pass checkpoint restore: {error}', file=sys.stderr)
    if metadata is None:
        metadata, _ = restore_pass(args)
        if stat_identity(args.input.stat()) != compressed:
            raise ValueError('checkpoint archive changed during restore')
        restore_pass(args, expected=metadata, apply=True, identities=identities)
    archive_sha256 = file_hash(args.input)
    if stat_identity(args.input.stat()) != compressed:
        raise ValueError('checkpoint archive changed during restore')
    write_json(args.root / '.lake/ci-cache' / (args.layer + '.json'), dict(metadata, archive_sha256=archive_sha256))
    if args.metadata:
        write_json(args.metadata, metadata)
    if local_state is not None:
        write_local_state(local_state, metadata, args.input, identities)
    emit({'layer': args.layer, 'generation': metadata['generation'],
          'files': len(metadata['entries']), 'restored': True, 'method': method}, args.github_output)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    for name in ('supported', 'context', 'pack', 'restore'):
        p = sub.add_parser(name)
        p.add_argument('--root', type=Path, default=Path.cwd())
        p.add_argument('--native-cache', type=Path)
        p.add_argument('--github-output', type=Path)
        if name == 'supported':
            p.add_argument('--materialized', action='store_true',
                           help='require every dependency config after source acquisition')
        if name in ('pack', 'restore'):
            p.add_argument('--layer', choices=LAYERS, required=True)
            p.add_argument('--metadata', type=Path)
            p.add_argument('--local-state', type=Path, help='reuse file hashes in the same quiescent checkout')
        if name == 'pack':
            p.add_argument('--output', type=Path, required=True)
            p.add_argument('--production-root', action='append', default=[])
        if name == 'restore':
            p.add_argument('--input', type=Path, required=True)
    args = parser.parse_args(argv)
    args.root = args.root.absolute()
    args.native_cache = (args.native_cache or Path(os.environ.get('LAKE_CACHE_DIR', args.root / '.lake/native-cache'))).absolute()
    try:
        supported(args.root, getattr(args, 'materialized', False))
        if args.action == 'supported':
            emit({'supported': True}, args.github_output)
        elif args.action == 'context':
            emit(contexts(args.root), args.github_output)
        elif args.action == 'pack':
            pack(args)
        else:
            restore(args)
        return 0
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError) as error:
        print('Checkpoint failed: ' + str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
