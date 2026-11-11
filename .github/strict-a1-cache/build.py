#!/usr/bin/env python3
"""Compile only the fixed 445 pinned dependency modules. No project proofs or replay."""
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import time
import tomllib

ROOT = Path.cwd().resolve()
HERE = ROOT / '.github/strict-a1-cache'
PLAN = json.loads((HERE / 'plan.json').read_text())
STACKS = ROOT / '.lake/packages/Stacks'
PRODUCTS = STACKS / '.lake/build/lib/lean'
OUT = ROOT / '.lake/strict-a1-result'
SUFFIXES = ('.olean', '.olean.server', '.olean.private', '.ilean', '.ir', '.ir.sig')
EXPECTED = {x['module']: x for x in PLAN['dependency_sources']}
PINS = {k: PLAN[k] for k in ('lean_version', 'lean_commit', 'mathlib_revision', 'stacks_revision')}


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def write(name, data):
    OUT.mkdir(parents=True, exist_ok=True)
    path = OUT / name
    temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(json.dumps(data, indent=2) + '\n')
    temp.replace(path)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def source(module):
    return STACKS / (module.replace('.', '/') + '.lean')


def imports(path):
    # Lex only the header. Comments or strings inside proof bodies are irrelevant.
    text = path.read_text()
    pos = 0
    def token():
        nonlocal pos
        while pos < len(text):
            if text[pos].isspace():
                pos += 1
            elif text.startswith('--', pos):
                end = text.find('\n', pos)
                pos = len(text) if end < 0 else end + 1
            elif text.startswith('/-', pos):
                pos += 2
                depth = 1
                while depth and pos < len(text):
                    if text.startswith('/-', pos):
                        depth += 1
                        pos += 2
                    elif text.startswith('-/', pos):
                        depth -= 1
                        pos += 2
                    else:
                        pos += 1
                require(depth == 0, 'Unclosed header comment: ' + str(path))
            else:
                match = re.match(r"[A-Za-z_][A-Za-z0-9_'.]*", text[pos:])
                if match:
                    pos += len(match[0])
                    return match[0]
                return None
        return None
    result = []
    current = token()
    while current in ('module', 'prelude'):
        current = token()
    while current is not None:
        while current in ('public', 'private', 'meta'):
            current = token()
        if current != 'import':
            break
        current = token()
        if current == 'all':
            current = token()
        require(current is not None, 'Missing imported module: ' + str(path))
        result.append(current)
        current = token()
        while current and current[0].isupper() and current not in ('module', 'prelude'):
            result.append(current)
            current = token()
    return result


def bundle(module):
    stem = PRODUCTS / module.replace('.', '/')
    paths = [Path(str(stem) + suffix) for suffix in SUFFIXES]
    for path in paths:
        require(path.is_file() and not path.is_symlink() and path.stat().st_size > 0,
                'Missing/nonregular required product: ' + str(path.relative_to(ROOT)))
    data = json.loads(paths[3].read_text())
    require(data['module'] == module, 'Incorrect ilean module identity: ' + module)
    actual = [item[0] for item in data['directImports']]
    expected = imports(source(module))
    require(actual == expected or actual == ['Init'] + expected,
            'Source/ilean imports differ: ' + module)
    return paths, data['directImports']


def initialize():
    require(len(EXPECTED) == 445, 'Expected exactly 445 authorized modules')
    require((ROOT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0', 'Wrong toolchain pin')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    resolved = {x['name']: x['rev'] for x in manifest['packages']}
    require(resolved['Stacks'] == PINS['stacks_revision'] and resolved['mathlib'] == PINS['mathlib_revision'], 'Wrong dependency pins')
    for package, pin in [('Stacks', PINS['stacks_revision']), ('mathlib', PINS['mathlib_revision'])]:
        actual = subprocess.check_output(['git', '-C', str(ROOT / '.lake/packages' / package), 'rev-parse', 'HEAD'], text=True).strip()
        require(actual == pin, 'Wrong materialized source commit: ' + package)
        dirty = subprocess.check_output(['git', '-C', str(ROOT / '.lake/packages' / package), 'status', '--porcelain', '--untracked-files=no'], text=True)
        require(not dirty.strip(), 'Dirty dependency source: ' + package)
    version = subprocess.check_output(['lean', '--version'], text=True).strip()
    require('4.35.0' in version and PINS['lean_commit'] in version, 'Unexpected compiler identity: ' + version)
    # Lake only resolves the environment. It never schedules a dependency build here.
    lean_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], text=True).strip()
    roots = [str((ROOT / p).resolve()) if not Path(p).is_absolute() else p for p in lean_path.split(os.pathsep) if p]
    prefix = subprocess.check_output(['lean', '--print-prefix'], text=True).strip()
    roots.append(str(Path(prefix) / 'lib/lean'))
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(roots))
    # Never transmit credentials into compiler child environments.
    for key in list(env):
        if any(word in key.upper() for word in ('TOKEN', 'SECRET', 'PASSWORD', 'CREDENTIAL')):
            env.pop(key)
    for module, entry in EXPECTED.items():
        require(sha(source(module)) == entry['source_sha256'], 'Changed pinned source: ' + module)
        require(imports(source(module)) == entry['source_imports'], 'Changed source header: ' + module)
    closure, pending, missing = set(), list(EXPECTED), []
    nonstacks = set()
    while pending:
        module = pending.pop()
        if module in closure:
            continue
        closure.add(module)
        require(source(module).is_file(), 'Unknown Stacks source: ' + module)
        for dep in imports(source(module)):
            if dep.startswith(('StacksCore.', 'StacksFrontier.', 'Stacks.')) or dep in ('StacksCore', 'StacksFrontier', 'Stacks'):
                pending.append(dep)
            else:
                nonstacks.add(dep)
    for module in sorted(closure - EXPECTED.keys()):
        try:
            bundle(module)
        except Exception as error:
            missing.append({'module': module, 'error': str(error)})
    for module in sorted(nonstacks):
        if not any((Path(root) / (module.replace('.', '/') + '.olean')).is_file() for root in roots):
            missing.append({'module': module, 'error': 'Missing non-Stacks imported olean'})
    write('preflight.json', {'pins': PINS, 'compiler': version, 'plan_sha256': PLAN['plan_sha256'],
          'plan_file_sha256': sha(HERE / 'plan.json'), 'authorized_count': 445,
          'stacks_transitive_closure_count': len(closure), 'reused_lower_count': len(closure) - 445,
          'missing_outside_authorized_set': missing})
    require(not missing, 'Exact prerequisite delta is in preflight.json; no expansion or build attempted')
    # The 306 selected baseline modules must retain the exact verified archive bytes.
    for item in PLAN['cached_entries']:
        path = ROOT / item['path']
        require(path.stat().st_size == item['size'] and sha(path) == item['sha256'],
                'Baseline member mismatch: ' + item['path'])
    # No authorized target should already have completed cached products silently.
    reused = {}
    for module in sorted(EXPECTED):
        if (PRODUCTS / (module.replace('.', '/') + '.olean')).exists():
            paths, direct = bundle(module)
            reused[module] = record(module, paths, direct, None, 'restored-exact-pinned-cache')
    options = tomllib.loads((STACKS / 'lakefile.toml').read_text()).get('leanOptions', {})
    opts = []
    def flatten(mapping, prefix=''):
        for key, value in mapping.items():
            name = prefix + key
            if isinstance(value, dict):
                yield from flatten(value, name + '.')
            else:
                yield name, value
    for key, value in flatten(options):
        if key.startswith('weak.'):
            key = key[5:]
        rendered = str(value).lower() if isinstance(value, bool) else str(value)
        opts.append('-D' + key + '=' + rendered)
    return env, opts, version, reused


def record(module, paths, direct, code, provenance):
    return {'module': module, 'source_path': module.replace('.', '/') + '.lean',
            'source_sha256': sha(source(module)), 'directImports': direct,
            'compiler_exit': code, 'provenance': provenance,
            'products': [{'path': p.relative_to(ROOT).as_posix(), 'size': p.stat().st_size,
                          'sha256': sha(p)} for p in paths]}


def compile_one(module, env, opts):
    stem = PRODUCTS / module.replace('.', '/')
    stem.parent.mkdir(parents=True, exist_ok=True)
    logfile = OUT / 'logs' / (module + '.log')
    logfile.parent.mkdir(parents=True, exist_ok=True)
    command = ['lean', '-j1', *opts, '-o', str(stem) + '.olean', '-i', str(stem) + '.ilean', str(source(module))]
    started = time.time()
    with logfile.open('w') as log:
        process = subprocess.run(command, cwd=STACKS, env=env, stdout=log, stderr=subprocess.STDOUT)
    require(process.returncode == 0, f'Compiler exit {process.returncode}: {module}\n' + logfile.read_text()[-12000:])
    paths, direct = bundle(module)
    require(sha(source(module)) == EXPECTED[module]['source_sha256'], 'Source changed during compilation')
    result = record(module, paths, direct, process.returncode, 'compiled-this-run')
    result.update(seconds=time.time() - started, command=command)
    return result


def main():
    started = time.time()
    results, failures = {}, []
    code, version = 1, None
    try:
        env, opts, version, results = initialize()
        remaining = set(EXPECTED) - results.keys()
        with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
            active = {}
            while remaining or active:
                if not failures:
                    ready = sorted(m for m in remaining if set(EXPECTED[m]['compile_predecessors']) <= results.keys())
                    for module in ready[:8 - len(active)]:
                        remaining.remove(module)
                        active[pool.submit(compile_one, module, env, opts)] = module
                if not active:
                    require(not remaining or failures, 'Dependency DAG stalled')
                    break
                done, _ = concurrent.futures.wait(active, return_when=concurrent.futures.FIRST_COMPLETED)
                for future in done:
                    module = active.pop(future)
                    try:
                        results[module] = future.result()
                        print(f'PASS {len(results)}/445 {module}', flush=True)
                    except Exception as error:
                        failures.append({'module': module, 'error': str(error)})
                        print('FAIL ' + str(error), flush=True)
                write('progress.json', {'completed': sorted(results), 'failures': failures, 'pending': sorted(remaining)})
        code = 0 if len(results) == 445 and not failures else 1
    except Exception as error:
        failures.append({'error': str(error)})
        print('FAIL ' + str(error), flush=True)
    producer = {'schema': 1, 'repository': os.environ.get('GITHUB_REPOSITORY'),
        'head': os.environ.get('GITHUB_SHA'), 'run_id': os.environ.get('GITHUB_RUN_ID'),
        'run_attempt': os.environ.get('GITHUB_RUN_ATTEMPT'), 'pins': PINS, 'compiler': version,
        'plan_sha256': PLAN['plan_sha256'], 'plan_file_sha256': sha(HERE / 'plan.json'),
        'lake_manifest_sha256': sha(ROOT / 'lake-manifest.json'),
        'stacks_config_sha256': sha(STACKS / 'lakefile.toml') if (STACKS / 'lakefile.toml').exists() else None,
        'build_true_exit': code, 'status': 'complete' if code == 0 else 'partial-or-failed',
        'authorized_count': 445, 'completed_count': len(results), 'seconds': time.time() - started,
        'failures': failures, 'modules': [results[m] for m in sorted(results)]}
    write('producer.json', producer)
    # Regular exact products only. No repository configuration, secrets or environment files.
    name = 'strict-a1-dependencies.tar'
    with tarfile.open(OUT / name, 'w', format=tarfile.PAX_FORMAT, dereference=True) as archive:
        archive.add(OUT / 'producer.json', arcname='producer.json', recursive=False)
        for module in sorted(results):
            for product in results[module]['products']:
                path = ROOT / product['path']
                require(path.is_file() and not path.is_symlink(), 'Unsafe artifact member')
                archive.add(path, arcname=product['path'], recursive=False)
    (OUT / (name + '.sha256')).write_text(sha(OUT / name) + '  ' + name + '\n')
    print(f'FINAL build_true_exit={code} complete={len(results)}/445', flush=True)
    return code


if __name__ == '__main__':
    sys.exit(main())
