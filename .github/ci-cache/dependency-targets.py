#!/usr/bin/env python3
"""Find external build targets for the Colib CI libraries with Lake's import graph."""
import json
from pathlib import Path
import subprocess
import sys

import checkpoint


def query(targets):
    if not targets:
        return []
    result = subprocess.run(['lake', '--no-build', 'query', '--json', *targets],
                            stdout=subprocess.PIPE, text=True)
    if result.returncode:
        sys.stderr.write(result.stdout)
        raise SystemExit(result.returncode)
    results = [json.loads(line) for line in result.stdout.splitlines()]
    if len(results) != len(targets):
        raise ValueError('Unexpected number of Lake query results')
    return results


def external_targets(libraries):
    root = Path.cwd()
    packages = checkpoint.dependencies(root)
    modules = set().union(*query([library + ':modules' for library in libraries]))
    pending = sorted(modules)
    targets = set()
    while pending:
        imports = set().union(*query(['+' + module + ':imports' for module in pending])) - modules
        pending = []
        names = sorted(imports)
        for name, source in zip(names, query(['+' + name + ':lean' for name in names]), strict=True):
            path = Path(source).resolve()
            if any(path.is_relative_to(package) for package in packages):
                targets.add(path.relative_to(root).as_posix())
            elif path.is_relative_to(root):
                pending.append(name)
            else:
                raise ValueError(f'Lake returned a module outside the pinned workspace: {source}')
        modules.update(imports)
    return sorted(targets)



def mathlib_build_state():
    build = Path('.lake/packages/mathlib/.lake/build')
    return {path.as_posix(): list(checkpoint.stat_identity(path.lstat()))
            for subtree in ('ir', 'lib/lean')
            for path in checkpoint.tree(build / subtree)}


if __name__ == '__main__':
    arguments = sys.argv[1:]
    if arguments == ['--snapshot-mathlib']:
        print(json.dumps(mathlib_build_state(), sort_keys=True))
    elif len(arguments) == 2 and arguments[0] == '--mathlib-delta':
        before = json.loads(Path(arguments[1]).read_text())
        for path, identity in sorted(mathlib_build_state().items()):
            if before.get(path) != identity:
                print(path)
    else:
        for target in external_targets(arguments):
            print(target)
