#!/usr/bin/env python3
"""Prepend Colib's admission policy to the pinned upstream webhook bundle."""
import hashlib
from pathlib import Path
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo


def main():
    root = Path(__file__).resolve().parent
    archive = root / 'lambdas/webhook.zip'
    hashes = {name: digest for digest, name in
              (line.split() for line in (root / 'lambdas.sha256').read_text().splitlines())}
    if hashlib.sha256(archive.read_bytes()).hexdigest() != hashes[archive.name]:
        raise ValueError('Unexpected upstream webhook digest')

    target = archive.with_name('warmup-webhook.zip')
    temporary = target.with_suffix('.tmp')
    try:
        with ZipFile(archive) as source, ZipFile(temporary, 'w') as bundle:
            if 'index.js' not in source.namelist() or 'upstream.js' in source.namelist():
                raise ValueError('Unexpected upstream webhook layout')
            for item in source.infolist():
                data = source.read(item)
                if item.filename == 'index.js':
                    item.filename = 'upstream.js'
                bundle.writestr(item, data)
            wrapper = ZipInfo('index.js')
            wrapper.create_system = 3
            wrapper.external_attr = 0o100644 << 16
            bundle.writestr(wrapper, (root / 'warmup-webhook.mjs').read_bytes(),
                            compress_type=ZIP_DEFLATED)
        temporary.replace(target)
    finally:
        temporary.unlink(missing_ok=True)


if __name__ == '__main__':
    main()
