"""GitHub Release transport for Stacks archives above the asset size limit."""
import hashlib
import json
from pathlib import Path
import re
import shutil
import tempfile

ASSET_LIMIT = 2 * 1024**3
VOLUME_BYTES = 1792 * 1024**2
INDEX_LIMIT = 128 * 1024
INDEX_NAME = re.compile(r'stacks-checkpoint-([0-9a-f]{64})\.parts\.json')
SHA256 = re.compile(r'[0-9a-f]{64}')
BLOCK_BYTES = 1024**2


def volume_name(archive_sha256, number):
    return f'stacks-checkpoint-{archive_sha256}.part-{number:04d}'


def file_identity(path):
    with path.open('rb') as stream:
        return path.stat().st_size, hashlib.file_digest(stream, 'sha256').hexdigest()


def read_index(index, local, assets):
    generation = INDEX_NAME.fullmatch(index['name'])[1]
    data = json.loads(local.read_bytes())
    if (not isinstance(data, dict) or data.get('version') != 1 or data.get('generation') != generation
            or type(data.get('size')) is not int or data['size'] <= 0
            or not isinstance(data.get('sha256'), str) or not SHA256.fullmatch(data['sha256'])
            or not isinstance(data.get('parts'), list) or not 2 <= len(data['parts']) < 1000):
        raise ValueError('invalid Stacks Release volume index')
    parts = []
    for number, part in enumerate(data['parts'], 1):
        if (not isinstance(part, dict) or type(part.get('size')) is not int
                or not 0 < part['size'] < ASSET_LIMIT
                or not isinstance(part.get('sha256'), str) or not SHA256.fullmatch(part['sha256'])):
            raise ValueError('invalid Stacks Release volume identity')
        name = volume_name(data['sha256'], number)
        asset = assets.get(name)
        if (asset is None or asset['size'] != part['size']
                or asset.get('digest') != 'sha256:' + part['sha256']):
            raise ValueError(f'missing or mismatched Stacks Release volume {name}')
        parts.append(asset)
    if sum(part['size'] for part in parts) != data['size']:
        raise ValueError('Stacks Release volume sizes do not match the index')
    return {**index, 'generation': generation, 'size': data['size'],
            'parts': parts, 'sha256': data['sha256']}


def copy_bytes(source, target, size, *digests):
    while size:
        block = source.read(min(size, BLOCK_BYTES))
        if not block:
            raise ValueError('unexpected end of Stacks checkpoint volume')
        target.write(block)
        for digest in digests:
            digest.update(block)
        size -= len(block)


def download(asset, output, fetch, *, prefix=False):
    parts = asset['parts']
    if prefix:
        fetch(dict(parts[0], checkpoint_size=asset['size']), output, prefix=True)
        return
    room = asset['size'] + max(part['size'] for part in parts)
    if shutil.disk_usage(output.parent).free < room:
        raise ValueError('insufficient disk space to assemble the Stacks Release checkpoint')
    digest = hashlib.sha256()
    with tempfile.TemporaryDirectory(prefix='stacks-release-volumes-', dir=output.parent) as scratch:
        directory = Path(scratch)
        assembled = directory / 'assembled'
        volume = directory / 'volume'
        with assembled.open('wb') as target:
            for part in parts:
                fetch(part, volume)
                with volume.open('rb') as source:
                    copy_bytes(source, target, part['size'], digest)
                volume.unlink()
        if assembled.stat().st_size != asset['size'] or digest.hexdigest() != asset['sha256']:
            raise ValueError('assembled Stacks checkpoint size or digest mismatch')
        assembled.replace(output)


def publish(archive, generation, directory, upload):
    size, archive_digest = file_identity(archive)
    if shutil.disk_usage(directory).free < min(size, VOLUME_BYTES):
        raise ValueError('insufficient disk space to split the Stacks Release checkpoint')
    count = (size + VOLUME_BYTES - 1) // VOLUME_BYTES
    if not 2 <= count < 1000:
        raise ValueError('Stacks checkpoint needs an unsupported number of Release volumes')
    parts = []
    checkpoint_digest = hashlib.sha256()
    with archive.open('rb') as source:
        for number in range(1, count + 1):
            path = directory / volume_name(archive_digest, number)
            length = min(VOLUME_BYTES, size - (number - 1) * VOLUME_BYTES)
            digest = hashlib.sha256()
            with path.open('wb') as target:
                copy_bytes(source, target, length, digest, checkpoint_digest)
            sha256 = digest.hexdigest()
            upload(path, {'size': length, 'digest': 'sha256:' + sha256})
            path.unlink()
            parts.append({'size': length, 'sha256': sha256})
        if source.read(1) or checkpoint_digest.hexdigest() != archive_digest:
            raise ValueError('Stacks checkpoint changed while splitting')
    index = directory / f'stacks-checkpoint-{generation}.parts.json'
    index.write_text(json.dumps({'version': 1, 'generation': generation, 'size': size,
                                 'sha256': archive_digest, 'parts': parts}, sort_keys=True) + '\n')
    index_size, index_digest = file_identity(index)
    if index_size > INDEX_LIMIT:
        raise ValueError('Stacks Release volume index exceeds its size limit')
    return index, {'size': index_size, 'digest': 'sha256:' + index_digest}
