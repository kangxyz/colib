#!/usr/bin/env python3
"""Restore the Stacks layer, filling missing coverage from its published baseline."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tarfile
import tempfile

import checkpoint

PREFIX_BYTES = 8 * 1024**2
RESTORE_ERRORS = (OSError, ValueError, KeyError, TypeError, AttributeError, tarfile.TarError)
DOWNLOAD_ERRORS = (*RESTORE_ERRORS, subprocess.CalledProcessError)


def published_asset():
    tag = f"stacks-checkpoint-{os.environ['STACKS_REVISION']}-{os.environ['STACKS_CONTEXT'][:16]}"
    repository = os.environ['GITHUB_REPOSITORY']
    result = subprocess.run(['gh', 'api', f'repos/{repository}/releases/tags/{tag}', '--jq', r'''
        select(.draft == false)
        | [.assets[] | select(.state == "uploaded" and
            (.name | test("^stacks-checkpoint-[0-9]+-[0-9]+[.]tar[.]zst$")))]
        | max_by([.size, .created_at])'''], text=True, capture_output=True)
    return json.loads(result.stdout or 'null') if result.returncode == 0 else None


def download(asset, output, *, prefix=False):
    repository = os.environ['GITHUB_REPOSITORY']
    api = os.environ['GITHUB_API_URL']
    url = f"{api}/repos/{repository}/releases/assets/{asset['id']}"
    limit = min(PREFIX_BYTES, asset['size']) if prefix else asset['size']
    command = ['curl', '--config', '-', '--location', '--fail', '--silent', '--show-error',
               '--connect-timeout', '15', '--max-time', '20' if prefix else '180',
               '--max-filesize', str(limit), '--header', 'Accept: application/octet-stream',
               '--output', str(output)]
    if prefix:
        command += ['--range', f'0-{limit - 1}']
    auth = f'header = "Authorization: Bearer {os.environ["GH_TOKEN"]}"\n'
    subprocess.run([*command, url], text=True, input=auth, check=True)
    if not prefix:
        if output.stat().st_size != limit:
            raise ValueError('published Stacks checkpoint size mismatch')
        if asset.get('digest') and asset['digest'] != 'sha256:' + checkpoint.file_hash(output):
            raise ValueError('published Stacks checkpoint digest mismatch')


def manifest(path, args):
    # The complete first member suffices for comparison. The real restore still
    # validates every member and checks the decompressor exit status.
    with checkpoint.archive_stream(path, False, header_only=True) as stream, \
            tarfile.open(fileobj=stream, mode='r|') as archive:
        data = checkpoint.read_metadata(archive, iter(archive))
    checkpoint.validate_metadata(data, args, set())
    return data


def covers(warm, published):
    if warm['generation'] == published['generation']:
        return True
    if len(warm['entries']) < len(published['entries']):
        return False
    entries = {(e['area'], e['path']): checkpoint.semantic(e) for e in warm['entries']}
    return all(entries.get((e['area'], e['path'])) == checkpoint.semantic(e)
               for e in published['entries'])


def apply(args, path):
    args.input = path
    try:
        checkpoint.restore(args)
    except RESTORE_ERRORS as error:
        print(f'::warning::Optional Stacks checkpoint could not be restored: {error}')
        return False
    return True


def restore_stacks(args, warm, asset):
    if asset is None:
        if warm.is_file():
            apply(args, warm)
        return

    local = None
    if warm.is_file():
        try:
            local = manifest(warm, args)
        except RESTORE_ERRORS as error:
            print(f'::warning::Optional Stacks checkpoint manifest could not be read: {error}')

    warm.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='stacks-baseline-', dir=warm.parent) as directory:
        baseline = Path(directory) / 'baseline.tar.zst'
        baseline_applied = False
        try:
            if local is not None:
                prefix = Path(directory) / 'prefix.tar.zst'
                try:
                    download(asset, prefix, prefix=True)
                    published = manifest(prefix, args)
                except DOWNLOAD_ERRORS:
                    print('Published Stacks manifest preview unavailable. Trying the full asset.')
                    download(asset, baseline)
                    published = manifest(baseline, args)
                if covers(local, published):
                    if apply(args, warm):
                        print('Restored the cached Stacks checkpoint once. It covers the published baseline.')
                        return
                    local = None
            if not baseline.is_file():
                download(asset, baseline)
            print(f"Using verified Stacks baseline {asset['name']} ({asset['size']} bytes).")
            baseline_applied = apply(args, baseline)
        except DOWNLOAD_ERRORS as error:
            print(f'::warning::Published Stacks baseline unavailable: {error}')

        # Overlay newer partial output last. A failed baseline download does not
        # prevent restoring the optional cache.
        if local is not None and apply(args, warm):
            return
        if baseline_applied:
            baseline.replace(warm)


def main():
    root = Path.cwd()
    args = argparse.Namespace(root=root, layer='stacks',
                              native_cache=Path(os.environ['LAKE_CACHE_DIR']).absolute(),
                              metadata=None, github_output=None)
    warm = Path(os.environ['GITHUB_WORKSPACE']) / os.environ['CI_CHECKPOINT_PATH'] / 'stacks.tar.zst'
    checkpoint.supported(root)
    restore_stacks(args, warm, published_asset())


if __name__ == '__main__':
    main()
