#!/usr/bin/env python3
"""Restore checked Colib native outputs and back up published archives."""

import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import tomllib
from urllib.parse import urlencode
import zipfile

from checkpoint import digest, file_hash as sha
from colib_r2 import ColibR2
from stage import read_map

COMMIT = re.compile(r'[0-9a-f]{40}')
DIGEST = re.compile(r'sha256:[0-9a-f]{64}')
NATIVE_FILE = re.compile(r'[0-9a-f]{16}(?:\.[A-Za-z0-9._+-]+)?')
ARTIFACTS = {'cache-staging', 'build-dependencies', 'build-stacks'}


def output(*command):
    return subprocess.check_output(command, text=True).strip()


def github(repository, endpoint, **parameters):
    query = '?' + urlencode(parameters) if parameters else ''
    return json.loads(output('gh', 'api', f'repos/{repository}/{endpoint}{query}'))


def repository_push(run, repository_id):
    return (run.get('event') == 'push' and run.get('path') == '.github/workflows/ci.yml'
            and (run.get('repository') or {}).get('id') == repository_id
            and (run.get('head_repository') or {}).get('id') == repository_id)


def checked_push(run, repository_id):
    return (repository_push(run, repository_id) and run.get('status') == 'completed'
            and run.get('conclusion') == 'success')


def source_commits(api, head, target, repository_id, parents):
    # A fast-forward may have the same single-parent head as a direct push.
    yield head
    if len(parents) == 2:
        yield parents[1]
    for pull in api(f'commits/{head}/pulls', per_page=20):
        source, base = pull.get('head', {}), pull.get('base', {})
        if (pull.get('merged_at') and pull.get('merge_commit_sha') == head
                and base.get('ref') == target
                and (base.get('repo') or {}).get('id') == repository_id
                and (source.get('repo') or {}).get('id') == repository_id):
            yield source.get('sha', '')


def find_seed(api, head, tree, target, repository_id, run_id, parents):
    seen = set()
    started = None
    merge_parent = parents[1] if len(parents) == 2 else None
    for commit in source_commits(api, head, target, repository_id, parents):
        if not COMMIT.fullmatch(commit) or commit in seen:
            continue
        seen.add(commit)
        # The Git parent identifies the merged revision. Lake rehashes the
        # merge inputs before using any of its cached outputs.
        if commit not in (head, merge_parent) and api(f'git/commits/{commit}')['tree']['sha'] != tree:
            continue
        for run in api('actions/workflows/ci.yml/runs', head_sha=commit,
                       event='push', status='success', per_page=10)['workflow_runs']:
            if (run.get('head_sha') != commit or not checked_push(run, repository_id)
                    or not run.get('head_branch') or run['head_branch'] == target):
                continue
            if started is None:
                started = api(f'actions/runs/{run_id}')['created_at']
            if not run.get('updated_at') or run['updated_at'] > started:
                continue
            artifacts = {}
            for item in api(f'actions/runs/{run["id"]}/artifacts', per_page=100)['artifacts']:
                origin = item.get('workflow_run') or {}
                name = item.get('name')
                if (name not in ARTIFACTS or item.get('expired') is not False
                        or origin.get('id') != run['id'] or origin.get('head_sha') != commit
                        or origin.get('repository_id') != repository_id
                        or origin.get('head_repository_id') != repository_id
                        or not DIGEST.fullmatch(item.get('digest') or '')
                        or type(item.get('id')) is not int or item['id'] <= 0
                        or type(item.get('size_in_bytes')) is not int or item['size_in_bytes'] <= 0):
                    continue
                if name in artifacts:
                    raise ValueError('multiple eligible artifacts named ' + name)
                artifacts[name] = item
            if 'cache-staging' in artifacts:
                return run, artifacts
    return None


def find_published_baseline(api, branch, repository_id, domain):
    runs = api('actions/workflows/ci.yml/runs', branch=branch, event='push',
               status='success', per_page=5)['workflow_runs']
    releases = {release['tag_name']: release for release in api('releases', per_page=20)
                if release.get('draft') is False}
    for run in runs:
        revision = run.get('head_sha') or ''
        if not checked_push(run, repository_id) or run.get('head_branch') != branch:
            continue
        if not COMMIT.fullmatch(revision):
            continue
        run_id, attempt = run.get('id'), run.get('run_attempt')
        if type(run_id) is not int or type(attempt) is not int or min(run_id, attempt) < 1:
            continue
        tag = 'lean-native-' + revision
        release = releases.get(tag)
        if not release or release.get('target_commitish') != revision:
            continue
        name = f'lake-native-cache-{domain}-{run_id}-{attempt}.tar'
        for asset in release['assets']:
            if (asset.get('name') == name and asset.get('state') == 'uploaded'
                    and DIGEST.fullmatch(asset.get('digest') or '')
                    and type(asset.get('size')) is int and asset['size'] > 0):
                return revision, tag, asset
    return None


def download_release(repository, tag, asset, directory):
    if shutil.disk_usage(directory).free < 3 * asset['size'] + 512 * 1024**2:
        raise ValueError('insufficient temporary space for ' + asset['name'])
    subprocess.run(['gh', 'release', 'download', tag, '--repo', repository,
                    '--pattern', asset['name'], '--dir', str(directory)], check=True)
    archive = directory / asset['name']
    if archive.stat().st_size != asset['size'] or 'sha256:' + sha(archive) != asset['digest']:
        raise ValueError('published Colib cache size or digest mismatch')
    return archive


def download(repository, item, directory, filename):
    # Keep each ZIP and its extracted checkpoint in a disposable directory.
    if shutil.disk_usage(directory).free < 3 * item['size_in_bytes'] + 512 * 1024**2:
        raise ValueError('insufficient temporary space for ' + item['name'])
    archive = directory / 'artifact.zip'
    with archive.open('xb') as target:
        subprocess.run(['gh', 'api', f'repos/{repository}/actions/artifacts/{item["id"]}/zip'],
                       stdout=target, check=True)
    if 'sha256:' + sha(archive) != item['digest']:
        raise ValueError('artifact digest mismatch for ' + item['name'])
    destination = directory / filename
    with zipfile.ZipFile(archive) as compressed:
        entries = compressed.infolist()
        if len(entries) != 1 or entries[0].filename != filename or entries[0].is_dir():
            raise ValueError('unexpected artifact member for ' + item['name'])
        with compressed.open(entries[0]) as source, destination.open('xb') as target:
            shutil.copyfileobj(source, target)
    archive.unlink()
    return destination


def unpack_native(archive, staging):
    staging.mkdir()
    with tarfile.open(archive, 'r:') as tar:
        for member in tar:
            name = member.name.removeprefix('./')
            if member.isdir() and name in ('', '.'):
                continue
            if not member.isreg() or (name not in ('outputs.jsonl', 'producer.json')
                                      and not NATIVE_FILE.fullmatch(name)):
                raise ValueError('unexpected native staging member ' + member.name)
            with tar.extractfile(member) as source, (staging / name).open('xb') as target:
                shutil.copyfileobj(source, target)


def validate_producer(staging, repository, revision, package, domain, compiler):
    producer = json.loads((staging / 'producer.json').read_text())
    expected = dict(repository=repository, revision=revision, package=package,
                    domain=domain, compiler=compiler)
    if not isinstance(producer, dict) or any(producer.get(key) != value for key, value in expected.items()):
        raise ValueError('native artifact producer does not match the verified build')


def native_domain():
    return '-'.join((os.environ['RUNNER_OS'], os.environ['RUNNER_ARCH'],
                     sha(Path('lean-toolchain'))[:16]))


def import_native(archive, staging, repository, revision, domain, *, force=False):
    unpack_native(archive, staging)
    archive.unlink()
    package = tomllib.loads(Path('lakefile.toml').read_text())['name']
    validate_producer(staging, repository, revision, package, domain, output('lean', '--version'))
    subprocess.run([sys.executable, '.github/ci-cache/stage.py', 'verify', '--root', '.',
                    '--staging', str(staging), '--native-cache', os.environ['LAKE_CACHE_DIR']],
                   check=True)
    command = ['lake', 'cache', 'unstage', str(staging)]
    if force:
        command.append('--force-overwrite')
    subprocess.run(command, check=True)
    with open(os.environ['GITHUB_OUTPUT'], 'a') as out:
        out.write('imported=true\n')


def restore_r2_baseline(api, repository, branch, repository_id, domain):
    mirror = ColibR2.configured(repository, branch)
    if mirror is None:
        return False
    with tempfile.TemporaryDirectory(prefix='colib-native-r2-index-', dir=os.environ['RUNNER_TEMP']) as tmp:
        entries = mirror.matching(domain, Path(tmp))
    for entry in entries:
        try:
            attempt_path = f'actions/runs/{entry["run_id"]}/attempts/{entry["attempt"]}'
            run = api(attempt_path)
            if (not repository_push(run, repository_id) or run.get('head_branch') != branch
                    or run.get('head_sha') != entry['revision'] or run.get('run_number') != entry['run_number']
                    or run.get('run_attempt') != entry['attempt'] or run.get('id') != entry['run_id']):
                raise ValueError('the Colib R2 archive has the wrong default-branch producer')
            if not checked_push(run, repository_id):
                # Publication can be interrupted after the audited archive was indexed.
                jobs = api(attempt_path + '/jobs', per_page=100)['jobs']
                verified = {job['name'] for job in jobs if job.get('status') == 'completed'
                            and job.get('conclusion') == 'success' and job.get('head_sha') == entry['revision']}
                if not {'lean / Build', 'lean / Test, lint and axiom audit'} <= verified:
                    raise ValueError('the Colib R2 producer did not pass Build and Test')
            with tempfile.TemporaryDirectory(prefix='colib-native-r2-', dir=os.environ['RUNNER_TEMP']) as tmp:
                directory = Path(tmp)
                archive = mirror.download(entry, directory)
                import_native(archive, directory / 'stage', repository, entry['revision'], domain)
            print(f'Imported published Colib native cache from R2 ({entry["revision"]}).', flush=True)
            return True
        except (OSError, ValueError, KeyError, TypeError, tarfile.TarError, subprocess.CalledProcessError) as error:
            print(f'::warning::Skipping Colib R2 cache {entry["revision"]}: {error}', flush=True)
    return False


def restore_published_baseline():
    if Path('.lake/ci-cache/root.json').is_file():
        print('Using the verified Colib root checkpoint.', flush=True)
        return
    repository = os.environ['GITHUB_REPOSITORY']
    branch = os.environ['DEFAULT_BRANCH']
    repository_id = int(os.environ['GITHUB_REPOSITORY_ID'])
    domain = native_domain()

    def api(endpoint, **parameters):
        return github(repository, endpoint, **parameters)

    try:
        if restore_r2_baseline(api, repository, branch, repository_id, domain):
            return
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        print(f'::warning::Colib R2 index unavailable: {error}', flush=True)
    seed = find_published_baseline(api, branch, repository_id, domain)
    if seed is None:
        print('No compatible published Colib baseline.', flush=True)
        return
    revision, tag, asset = seed
    with tempfile.TemporaryDirectory(prefix='colib-native-', dir=os.environ['RUNNER_TEMP']) as tmp:
        directory = Path(tmp)
        archive = download_release(repository, tag, asset, directory)
        import_native(archive, directory / 'stage', repository, revision, domain)
    print(f'Imported published Colib native cache {revision} ({asset["name"]}).', flush=True)


def archive_content(archive, directory, repository, revision, domain):
    staging = directory / 'stage'
    unpack_native(archive, staging)
    producer = json.loads((staging / 'producer.json').read_bytes())
    if (not isinstance(producer, dict) or producer.get('repository') != repository
            or producer.get('revision') != revision or producer.get('domain') != domain
            or producer.get('package') != 'Colib'
            or not isinstance(producer.get('compiler'), str) or not producer['compiler']):
        raise ValueError('native archive has an invalid Colib producer identity')
    bindings = {}
    read_map(staging / 'outputs.jsonl', bindings)
    files = {path.name: sha(path) for path in staging.iterdir() if NATIVE_FILE.fullmatch(path.name)}
    if files.keys() != set(bindings.values()):
        raise ValueError('native archive and Colib output map differ')
    return digest({'compiler': producer['compiler'], 'mapping': bindings, 'files': files})


def publish_r2_baseline(archive, domain):
    repository = os.environ['GITHUB_REPOSITORY']
    branch = os.environ['DEFAULT_BRANCH']
    if os.environ['GITHUB_EVENT_NAME'] != 'push' or os.environ['GITHUB_REF'] != 'refs/heads/' + branch:
        raise ValueError('Colib R2 publishing requires a default-branch push')
    mirror = ColibR2.configured(repository, branch)
    if mirror is None:
        raise ValueError('Colib R2 publishing requires the CI cache bucket and write credentials')
    revision = os.environ['GITHUB_SHA']
    run_id, attempt = int(os.environ['GITHUB_RUN_ID']), int(os.environ['GITHUB_RUN_ATTEMPT'])
    release = github(repository, f'releases/tags/lean-native-{revision}')
    if release['draft'] or release['target_commitish'] != revision:
        raise ValueError('Colib Release has the wrong producer revision')
    name = f'lake-native-cache-{domain}-{run_id}-{attempt}.tar'
    asset = next((item for item in release['assets']
                  if item['name'] == name and item['state'] == 'uploaded'
                  and DIGEST.fullmatch(item.get('digest') or '')), None)
    if asset is None or archive.name != name or archive.stat().st_size != asset['size']:
        raise ValueError('Colib R2 backup has no matching verified Release asset')
    with tempfile.TemporaryDirectory(prefix='colib-r2-publish-', dir=os.environ['RUNNER_TEMP']) as tmp:
        directory = Path(tmp)
        entry = {
            'revision': revision, 'domain': domain, 'sha256': asset['digest'].removeprefix('sha256:'),
            'size': asset['size'], 'run_id': run_id, 'run_number': int(os.environ['GITHUB_RUN_NUMBER']),
            'attempt': attempt, 'content_sha256': archive_content(archive, directory, repository, revision, domain),
        }
        mirror.publish(archive, entry, directory)


def restore_layer(layer, archive, native_cache):
    receipt = Path('.lake/ci-cache') / (layer + '.json')
    try:
        restored = json.loads(receipt.read_text())
    except (OSError, ValueError):
        restored = {}
    if isinstance(restored, dict) and restored.get('archive_sha256') == sha(archive):
        print(f'{layer} already restored from the identical archive', flush=True)
        return
    subprocess.run([sys.executable, '.github/ci-cache/checkpoint.py', 'restore',
                    '--root', '.', '--layer', layer, '--input', str(archive),
                    '--native-cache', native_cache], check=True)


def main():
    repository = os.environ['GITHUB_REPOSITORY']
    repository_id = int(os.environ['GITHUB_REPOSITORY_ID'])
    target = os.environ['GITHUB_REF_NAME']
    head = os.environ['GITHUB_SHA']
    if output('git', 'rev-parse', 'HEAD') != head:
        raise ValueError('checkout differs from the target push')
    tree = output('git', 'rev-parse', 'HEAD^{tree}')
    header = output('git', 'cat-file', 'commit', 'HEAD').split('\n\n', 1)[0]
    parents = [line.removeprefix('parent ') for line in header.splitlines()
               if line.startswith('parent ')]

    def api(endpoint, **parameters):
        return github(repository, endpoint, **parameters)

    seed = find_seed(api, head, tree, target, repository_id, int(os.environ['GITHUB_RUN_ID']), parents)
    if seed is None:
        print('No matching checked branch build for this push.', flush=True)
        return
    run, artifacts = seed
    native_cache = os.environ['LAKE_CACHE_DIR']
    temporary_root = os.environ['RUNNER_TEMP']
    errors = (OSError, ValueError, KeyError, TypeError, zipfile.BadZipFile,
              tarfile.TarError, subprocess.CalledProcessError)
    with tempfile.TemporaryDirectory(prefix='merge-native-', dir=temporary_root) as temporary:
        directory = Path(temporary)
        archive = download(repository, artifacts['cache-staging'], directory, 'lake-native-cache.tar')
        import_native(archive, directory / 'stage', repository, run['head_sha'], native_domain(),
                      force=True)
    print(f'Imported native merge seed from run {run["id"]} ({run["head_sha"]}).', flush=True)
    for layer, filename in (('dependencies', 'build-dependencies.tar.zst'), ('stacks', 'stacks.tar.zst')):
        artifact = artifacts.get('build-' + layer)
        if artifact is None:
            continue
        try:
            with tempfile.TemporaryDirectory(prefix='merge-checkpoint-', dir=temporary_root) as temporary:
                archive = download(repository, artifact, Path(temporary), filename)
                restore_layer(layer, archive, native_cache)
        except errors as error:
            print(f'::warning::Skipped the branch {layer} checkpoint: {error}', flush=True)


if __name__ == '__main__':
    if sys.argv[1:] == ['--published-baseline']:
        restore_published_baseline()
    elif len(sys.argv) == 4 and sys.argv[1] == '--publish-r2':
        publish_r2_baseline(Path(sys.argv[2]), sys.argv[3])
    elif len(sys.argv) == 1:
        main()
    else:
        raise SystemExit('usage: merge_seed.py [--published-baseline | --publish-r2 ARCHIVE DOMAIN]')
