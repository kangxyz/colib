#!/usr/bin/env python3
"""Restore and publish the shared Stacks checkpoint."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile

import checkpoint
import stacks_release_volumes as volumes
from r2_storage import MAX_ARCHIVE_BYTES, WRITE_CONFLICT
from stacks_r2 import RETAINED_GENERATIONS, R2Cache, preview_bytes

RESTORE_ERRORS = (OSError, ValueError, KeyError, TypeError, AttributeError, tarfile.TarError)
DOWNLOAD_ERRORS = (*RESTORE_ERRORS, subprocess.CalledProcessError)
LEGACY_ASSET = re.compile(r'stacks-checkpoint-[0-9]+-[0-9]+\.tar\.zst')
GENERATION_ASSET = re.compile(r'stacks-checkpoint-([0-9a-f]{64})\.tar\.zst')


def release_tag(revision, context):
    return f'stacks-checkpoint-{revision}-{context[:16]}'


def github_release(tag):
    repository = os.environ['GITHUB_REPOSITORY']
    result = subprocess.run(['gh', 'api', f'repos/{repository}/releases/tags/{tag}'],
                            text=True, capture_output=True)
    if result.returncode:
        if '(HTTP 404)' in result.stderr:
            return None
        raise OSError(f'GitHub Stacks Release lookup failed: {result.stderr.strip()}')
    release = json.loads(result.stdout)
    return None if release['draft'] else release


def release_assets(release):
    return [asset for asset in (release or {}).get('assets', [])
            if asset['state'] == 'uploaded' and asset['size'] > 0
            and (LEGACY_ASSET.fullmatch(asset['name']) or GENERATION_ASSET.fullmatch(asset['name']))]


def asset_priority(asset):
    return asset['size'], asset['created_at']


def release_indexes(release, directory, generation=None):
    assets = {asset['name']: asset for asset in (release or {}).get('assets', [])
              if asset['state'] == 'uploaded' and asset['size'] > 0}
    for asset in assets.values():
        if (not volumes.INDEX_NAME.fullmatch(asset['name']) or asset['size'] > volumes.INDEX_LIMIT
                or (generation is not None and asset['name'] != f'stacks-checkpoint-{generation}.parts.json')
                or not re.fullmatch(r'sha256:[0-9a-f]{64}', asset.get('digest') or '')):
            continue
        index = directory / 'release-parts.json'
        try:
            download_file(asset, index)
            yield volumes.read_index(asset, index, assets)
        except DOWNLOAD_ERRORS as error:
            print(f'::warning::Skipping Stacks Release index {asset["name"]}: {error}')


def published_assets(directory):
    tag = release_tag(os.environ['STACKS_REVISION'], os.environ['STACKS_CONTEXT'])
    release = github_release(tag)
    assets = [dict(asset, generation=match[1]) if (match := GENERATION_ASSET.fullmatch(asset['name']))
              else asset for asset in release_assets(release)]
    single_file = max(assets, key=asset_priority, default=None)
    split = list(release_indexes(release, directory))
    if single_file is not None:
        split.append(single_file)
    yield from sorted(split, key=asset_priority, reverse=True)


def published_generation(revision, context, generation, directory):
    found = {'r2_exists': False, 'release_exists': False}
    try:
        r2 = R2Cache.configured(revision, context)
        if r2 is not None:
            index, _ = r2.current(directory / 'current.json')
            found['r2_exists'] = (index is not None and index['generation'] == generation
                                  and r2.archive_exists(index))
    except DOWNLOAD_ERRORS as error:
        print(f'::warning::Could not check the published R2 Stacks generation: {error}', flush=True)
    try:
        release = github_release(release_tag(revision, context))
        name = f'stacks-checkpoint-{generation}.tar.zst'
        found['release_exists'] = any(
            asset['name'] == name and re.fullmatch(r'sha256:[0-9a-f]{64}', asset.get('digest') or '')
            for asset in release_assets(release)) or any(release_indexes(release, directory, generation))
    except DOWNLOAD_ERRORS as error:
        print(f'::warning::Could not check the published GitHub Stacks generation: {error}', flush=True)
    return found


def download(asset, output, *, prefix=False):
    if 'parts' in asset:
        volumes.download(asset, output, download_file, prefix=prefix)
    else:
        download_file(asset, output, prefix=prefix)


def download_file(asset, output, *, prefix=False):
    repository = os.environ['GITHUB_REPOSITORY']
    api = os.environ['GITHUB_API_URL']
    url = f"{api}/repos/{repository}/releases/assets/{asset['id']}"
    limit = min(asset['size'], preview_bytes(asset.get('checkpoint_size', asset['size']))) if prefix else asset['size']
    command = ['curl', '--config', '-', '--location', '--fail', '--silent', '--show-error',
               '--connect-timeout', '15', '--max-time', '20' if prefix else '180',
               '--max-filesize', str(limit), '--header', 'Accept: application/octet-stream',
               '--output', str(output)]
    if prefix:
        command += ['--range', f'0-{limit - 1}']
    auth = f'header = "Authorization: Bearer {os.environ["GH_TOKEN"]}"\n'
    subprocess.run([*command, url], text=True, input=auth, check=True)
    if output.stat().st_size != limit:
        raise ValueError('published Stacks checkpoint size mismatch')
    if not prefix and asset.get('digest') and asset['digest'] != 'sha256:' + checkpoint.file_hash(output):
        raise ValueError('published Stacks checkpoint digest mismatch')


def read_manifest(path):
    # The complete first member suffices for comparison. The real restore still
    # validates every member and checks the decompressor exit status.
    with checkpoint.archive_stream(path, False, header_only=True) as stream, \
            tarfile.open(fileobj=stream, mode='r|') as archive:
        return checkpoint.read_metadata(archive, iter(archive))


def manifest(path, args):
    data = read_manifest(path)
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


def check_generation(asset, data):
    if asset.get('generation', data['generation']) != data['generation']:
        raise ValueError('published Stacks checkpoint generation mismatch')
    return data


def preview(args, asset, fetch, directory):
    prefix = directory / 'prefix.tar.zst'
    try:
        fetch(asset, prefix, prefix=True)
        data = manifest(prefix, args)
    except DOWNLOAD_ERRORS:
        print('Published Stacks manifest preview unavailable. Trying the full archive.')
        baseline = directory / 'baseline.tar.zst'
        fetch(asset, baseline)
        data = manifest(baseline, args)
    return check_generation(asset, data)


def restore_baseline(args, warm, local, asset, fetch, directory, source):
    baseline = directory / 'baseline.tar.zst'
    baseline.unlink(missing_ok=True)
    if local is not None:
        covered = local['generation'] == asset.get('generation')
        if covered or covers(local, preview(args, asset, fetch, directory)):
            if apply(args, warm):
                print(f'Restored the cached Stacks checkpoint once. It covers the {source} baseline.')
                return True
            local = None
    if not baseline.is_file():
        fetch(asset, baseline)
    if 'generation' in asset:
        check_generation(asset, manifest(baseline, args))
    print(f"Using verified Stacks baseline from {source} ({asset['size']} bytes).")
    if not apply(args, baseline):
        return False
    # Overlay newer partial output last. Keep the baseline archive if the
    # warm checkpoint is absent or could not be applied.
    if local is None or not apply(args, warm):
        baseline.replace(warm)
    return True


def restore_stacks(args, warm, r2=None):
    local = None
    if warm.is_file():
        try:
            local = manifest(warm, args)
        except RESTORE_ERRORS as error:
            print(f'::warning::Optional Stacks checkpoint manifest could not be read: {error}')

    warm.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='stacks-baseline-', dir=warm.parent) as scratch:
        directory = Path(scratch)
        if r2 is not None:
            try:
                index, _ = r2.current(directory / 'current.json')
                if index is not None and restore_baseline(args, warm, local, index, r2.download, directory, 'R2'):
                    return
            except DOWNLOAD_ERRORS as error:
                print(f'::warning::Published Stacks baseline from R2 unavailable: {error}')
        try:
            for asset in published_assets(directory):
                try:
                    if restore_baseline(args, warm, local, asset, download, directory, 'GitHub Release'):
                        return
                except DOWNLOAD_ERRORS as error:
                    print(f'::warning::Published Stacks baseline from GitHub Release unavailable: {error}')
        except DOWNLOAD_ERRORS as error:
            print(f'::warning::Published Stacks baseline from GitHub Release unavailable: {error}')
    if local is not None:
        apply(args, warm)


def legacy_release_contains(args, archive, generation, assets):
    if not assets:
        return False
    if any(asset.get('digest') for asset in assets):
        digest = 'sha256:' + checkpoint.file_hash(archive)
        if any(asset.get('digest') == digest for asset in assets):
            return True

    with tempfile.TemporaryDirectory(prefix='stacks-release-preview-', dir=archive.parent) as scratch:
        def matches(asset):
            prefix = Path(scratch) / f"{asset['id']}.tar.zst"
            try:
                try:
                    download(asset, prefix, prefix=True)
                except subprocess.CalledProcessError as error:
                    # A timeout may still leave enough of the prefix to read
                    # the complete first tar member.
                    if error.returncode != 28 or not prefix.is_file():
                        raise
                data = read_manifest(prefix)
                if data['generation'] != generation:
                    return False
                checkpoint.validate_metadata(data, args, set())
                return True
            finally:
                prefix.unlink(missing_ok=True)

        # Most retries match the published fallback, so read that one first.
        preferred, *other = sorted(assets, key=asset_priority, reverse=True)
        unreadable = None
        try:
            if matches(preferred):
                return True
        except DOWNLOAD_ERRORS as error:
            unreadable = error
        with ThreadPoolExecutor(max_workers=6) as pool:
            pending = [pool.submit(matches, asset) for asset in other]
            for result in as_completed(pending):
                try:
                    if result.result():
                        for task in pending:
                            task.cancel()
                        return True
                except DOWNLOAD_ERRORS as error:
                    unreadable = error
        if unreadable is not None:
            print(f'::warning::Some legacy Stacks Release generations could not be read: {unreadable}')
    return False


def publish_volumes(archive, generation, tag, release, directory):
    repository = os.environ['GITHUB_REPOSITORY']
    if release is None:
        create = ['gh', 'release', 'create', tag, '--repo', repository, '--target', os.environ['GITHUB_SHA'],
                  '--latest=false', '--title', 'Stacks compilation checkpoint',
                  '--notes', 'Independent Stacks working-build checkpoint from successful Colib native checks.']
        result = subprocess.run(create, text=True, capture_output=True)
        if result.returncode and github_release(tag) is None:
            raise OSError(f'Could not create the Stacks Release: {result.stderr.strip()}')

    def upload(path, identity, *, index=False):
        def existing():
            current = github_release(tag)
            if current is None:
                raise OSError(f'Stacks Release disappeared during publication: {tag}')
            return next((asset for asset in current['assets'] if asset['name'] == path.name), None)

        def complete(asset):
            if asset is None or asset['state'] != 'uploaded':
                return False
            if asset['size'] == identity['size'] and asset.get('digest') == identity['digest']:
                return True
            if index:
                return any(item['generation'] == generation for item in release_indexes(github_release(tag), directory))
            raise ValueError(f'existing Stacks Release volume has unexpected bytes: {path.name}')

        asset = existing()
        command = ['gh', 'release', 'upload', tag, str(path), '--repo', repository]
        for _ in range(2):
            if complete(asset):
                return
            if asset is not None and asset['state'] == 'starter':
                delete_release_asset(asset['id'])
            result = subprocess.run(command, text=True, capture_output=True)
            asset = existing()
            if complete(asset):
                return
            if asset is None or asset['state'] != 'starter':
                break
        raise OSError(f'Could not publish Stacks Release asset {path.name}: {result.stderr.strip()}')

    index, identity = volumes.publish(archive, generation, directory, upload)
    upload(index, identity, index=True)


def publish_release(args, archive, revision, context):
    candidate = manifest(archive, args)
    if not candidate['entries']:
        raise ValueError('cannot publish an empty Stacks checkpoint')
    generation = candidate['generation']
    name = f'stacks-checkpoint-{generation}.tar.zst'
    tag = release_tag(revision, context)
    release = github_release(tag)
    assets = release_assets(release)
    if any(asset['name'] == name for asset in assets) or legacy_release_contains(
            args, archive, generation, [asset for asset in assets if LEGACY_ASSET.fullmatch(asset['name'])]):
        print(f'GitHub Release already has Stacks checkpoint generation {generation[:12]}.')
        return

    repository = os.environ['GITHUB_REPOSITORY']
    with tempfile.TemporaryDirectory(prefix='stacks-release-publish-', dir=archive.parent) as scratch:
        directory = Path(scratch)
        if any(release_indexes(release, directory, generation)):
            print(f'GitHub Release already has Stacks checkpoint generation {generation[:12]}.')
            return
        if archive.stat().st_size >= volumes.ASSET_LIMIT:
            publish_volumes(archive, generation, tag, release, directory)
            print(f'Published Stacks checkpoint generation {generation[:12]} to GitHub Release in volumes.')
            return
        asset = directory / name
        asset.hardlink_to(archive)
        upload = ['gh', 'release', 'upload', tag, str(asset), '--repo', repository]
        create = ['gh', 'release', 'create', tag, str(asset), '--repo', repository,
                  '--target', os.environ['GITHUB_SHA'], '--latest=false',
                  '--title', 'Stacks compilation checkpoint',
                  '--notes', 'Independent Stacks working-build checkpoint from successful Colib native checks.']
        result = subprocess.run(upload if release is not None else create, text=True, capture_output=True)
        if result.returncode and release is None:
            release = github_release(tag)
            if release is not None and not any(item['name'] == name for item in release_assets(release)):
                result = subprocess.run(upload, text=True, capture_output=True)
        if result.returncode:
            if any(item['name'] == name for item in release_assets(github_release(tag))):
                print(f'GitHub Release already has Stacks checkpoint generation {generation[:12]}.')
                return
            raise OSError(f'GitHub Stacks Release publication failed: {result.stderr.strip()}')
    print(f'Published Stacks checkpoint generation {generation[:12]} to GitHub Release.')


def delete_release_asset(asset_id):
    repository = os.environ['GITHUB_REPOSITORY']
    result = subprocess.run(['gh', 'api', '--method', 'DELETE',
                             f'repos/{repository}/releases/assets/{asset_id}'],
                            text=True, capture_output=True)
    if result.returncode and '(HTTP 404)' not in result.stderr:
        raise OSError(f'Could not remove Stacks Release asset {asset_id}: {result.stderr.strip()}')


def prune_release(tag, generation, directory):
    release = github_release(tag)
    single = release_assets(release)
    split = list(release_indexes(release, directory))
    represented = [(match[1], asset) for asset in single if (match := GENERATION_ASSET.fullmatch(asset['name']))]
    represented.extend((asset['generation'], asset) for asset in split)
    # A broken or unreadable index cannot authorize deleting an older fallback.
    if len(split) != sum(bool(volumes.INDEX_NAME.fullmatch(asset['name']))
                         for asset in (release or {}).get('assets', []) if asset['state'] == 'uploaded'):
        raise ValueError('cannot prune a Stacks Release with an unreadable volume index')
    ordered = sorted(represented, key=lambda item: item[1]['created_at'], reverse=True)
    keep_generations = set()
    keep_ids = set()
    for identity, asset in ordered:
        if identity in keep_generations or len(keep_generations) >= RETAINED_GENERATIONS:
            continue
        keep_generations.add(identity)
        keep_ids.add(asset['id'])
        keep_ids.update(part['id'] for part in asset.get('parts', []))
    if generation not in keep_generations or len(keep_generations) != RETAINED_GENERATIONS:
        return
    # Two complete named generations supersede the historical run-named files.
    obsolete = [asset for asset in single + split if asset['id'] not in keep_ids]
    # Remove an obsolete split index before any of its parts. Unindexed uploads
    # belong to a publisher that may still be finishing or retrying.
    obsolete.sort(key=lambda asset: not bool(asset.get('parts')))
    for asset in obsolete:
        ids = [asset['id'], *(part['id'] for part in asset.get('parts', []))]
        for asset_id in ids:
            if asset_id not in keep_ids:
                delete_release_asset(asset_id)
        print(f'Pruned obsolete Stacks Release asset {asset["name"]}.', flush=True)


def publish_r2(args, archive, r2):
    size = archive.stat().st_size
    if not 0 < size <= MAX_ARCHIVE_BYTES:
        raise ValueError('Stacks archive exceeds the R2 single-request upload limit or is empty')
    candidate = manifest(archive, args)
    if not candidate['entries']:
        raise ValueError('cannot publish an empty Stacks checkpoint')
    index = None
    uploaded = False
    with tempfile.TemporaryDirectory(prefix='stacks-r2-publish-', dir=archive.parent) as scratch:
        directory = Path(scratch)
        current_path = directory / 'current.json'
        pointer = directory / 'next.json'
        for _ in range(3):
            current, etag = r2.current(current_path)
            if current is not None:
                if candidate['generation'] == current['generation'] and r2.archive_exists(current):
                    print('R2 already has this Stacks checkpoint generation.')
                    return
                if candidate['generation'] != current['generation']:
                    (directory / 'baseline.tar.zst').unlink(missing_ok=True)
                    if not covers(candidate, preview(args, current, r2.download, directory)):
                        print('Keeping the R2 Stacks baseline. The new checkpoint does not cover it.')
                        return
            if index is None:
                args.input = archive
                if checkpoint.restore(args, verify_only=True) != candidate:
                    raise ValueError('Stacks checkpoint changed during publication')
                index = {'schema': 1, 'revision': r2.revision, 'context': r2.context,
                         'generation': candidate['generation'], 'size': size,
                         'sha256': checkpoint.file_hash(archive)}
            if not uploaded:
                stored = r2.store_archive(index, archive)
                if stored is None:
                    continue
                index = stored
                uploaded = True
            next_pointer = dict(index)
            if current is not None:
                previous = (current['generation'] if current['generation'] != index['generation']
                            else current.get('previous_generation'))
                if previous is not None:
                    next_pointer['previous_generation'] = previous
            checkpoint.write_json(pointer, next_pointer)
            condition = f'If-Match: {etag}' if etag else 'If-None-Match: *'
            status = r2.put('current.json', pointer, checkpoint.file_hash(pointer), condition, seconds=20)
            if status not in WRITE_CONFLICT:
                print(f"Published Stacks baseline to R2 ({index['size']} bytes, {index['generation'][:12]}).")
                return
    raise OSError('R2 Stacks baseline changed concurrently during publication')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    publish = parser.add_mutually_exclusive_group()
    publish.add_argument('--publish-r2', type=Path, metavar='ARCHIVE')
    publish.add_argument('--publish-release', type=Path, metavar='ARCHIVE')
    publish.add_argument('--check-published', metavar='GENERATION')
    publish.add_argument('--prune-r2', action='store_true')
    publish.add_argument('--prune-release', metavar='GENERATION')
    command = parser.parse_args()
    root = Path.cwd()
    args = argparse.Namespace(root=root, layer='stacks',
                              native_cache=Path(os.environ.get('LAKE_CACHE_DIR', root / '.lake/native-cache')).absolute(),
                              metadata=None, github_output=None)
    if state := os.environ.get('STACKS_LOCAL_STATE'):
        args.local_state = Path(state)
    checkpoint.supported(root)
    if any(vars(command).values()):
        context = checkpoint.contexts(root)['stacks_context']
        packages = json.loads((root / 'lake-manifest.json').read_text())['packages']
        revision = next(package['rev'] for package in packages if package['name'] == 'Stacks')
        try:
            generation = command.check_published if command.check_published is not None else command.prune_release
            if generation is not None and not re.fullmatch(r'[0-9a-f]{64}', generation):
                raise ValueError('invalid Stacks checkpoint generation')
            if command.check_published is not None:
                with tempfile.TemporaryDirectory(prefix='stacks-publish-check-') as scratch:
                    result = published_generation(revision, context, generation, Path(scratch))
                    checkpoint.emit(result, os.environ.get('GITHUB_OUTPUT'))
                return
            if command.prune_release is not None:
                with tempfile.TemporaryDirectory(prefix='stacks-release-prune-') as scratch:
                    prune_release(release_tag(revision, context), generation, Path(scratch))
                return
            if command.publish_release is not None:
                publish_release(args, command.publish_release, revision, context)
                return
            r2 = R2Cache.configured(revision, context)
            if r2 is None:
                raise ValueError('R2 endpoint, bucket and write credentials are required')
            if command.prune_r2:
                with tempfile.TemporaryDirectory(prefix='stacks-r2-prune-') as scratch:
                    r2.prune_archives(Path(scratch))
            else:
                publish_r2(args, command.publish_r2, r2)
        except DOWNLOAD_ERRORS as error:
            parser.exit(1, f'Could not publish or prune the Stacks checkpoint: {error}\n')
        return
    try:
        r2 = R2Cache.configured(os.environ['STACKS_REVISION'], os.environ['STACKS_CONTEXT'])
    except ValueError as error:
        print(f'::warning::R2 Stacks cache configuration ignored: {error}')
        r2 = None
    warm = Path(os.environ['GITHUB_WORKSPACE']) / os.environ['CI_CHECKPOINT_PATH'] / 'stacks.tar.zst'
    restore_stacks(args, warm, r2)


if __name__ == '__main__':
    main()
