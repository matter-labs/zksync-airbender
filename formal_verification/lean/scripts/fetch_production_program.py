#!/usr/bin/env python3
"""Fetch the pinned public ZKsync OS text and image for decoder comparisons."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import urllib.request


def verify(path, asset):
    if path.stat().st_size != asset['size']:
        raise ValueError(f"{asset['name']}: production asset size differs")
    if hashlib.sha256(path.read_bytes()).hexdigest() != asset['sha256']:
        raise ValueError(f"{asset['name']}: production asset hash differs")


def fetch(destination, manifest):
    destination.mkdir(parents=True, exist_ok=True)
    for asset in manifest['assets']:
        name = asset['name']
        if Path(name).name != name or name not in ('multiblock_batch.bin', 'multiblock_batch.text'):
            raise ValueError('unexpected production asset name')
        path = destination / name
        if path.exists():
            verify(path, asset)
        else:
            temporary = None
            try:
                with tempfile.NamedTemporaryFile(dir=destination, delete=False) as output:
                    temporary = Path(output.name)
                    with urllib.request.urlopen(asset['url'], timeout=60) as response:
                        size = 0
                        while chunk := response.read(131072):
                            size += len(chunk)
                            if size > asset['size']:
                                raise ValueError(f'{name}: production download exceeds pinned size')
                            output.write(chunk)
                verify(temporary, asset)
                os.replace(temporary, path)
            finally:
                if temporary is not None:
                    temporary.unlink(missing_ok=True)
        print(f"PASS {name} {asset['sha256']}", flush=True)
    return destination / 'multiblock_batch.text'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--destination', type=Path, required=True)
    parser.add_argument('--manifest', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'artifacts/programs/zksync-os.json')
    args = parser.parse_args()
    fetch(args.destination, json.loads(args.manifest.read_text()))


if __name__ == '__main__':
    main()
