#!/usr/bin/env python3
"""Export each imported native setup and compare its complete canonical bytes.

The exporter uses the current Rust tables. Each run uses a scratch directory.
The imported setup inventory comes from the Lake input declarations.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import struct
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_circuit_json import setup_paths


def compare_artifact(fresh, expected):
    # The exporter can add whitespace. The retained format is compact JSON with no newline.
    canonical = json.dumps(json.loads(fresh.read_bytes()), separators=(',', ':'), allow_nan=False).encode()
    if canonical != expected.read_bytes():
        raise ValueError(f'Native setup differs from imported bytes: {expected.name}')


def check(exporter):
    paths = setup_paths()
    if not paths:
        raise ValueError('No imported setups found')
    environment = dict(os.environ, RAYON_NUM_THREADS='1')
    repository = Path(__file__).resolve().parents[3]
    with tempfile.TemporaryDirectory(prefix='airbender-setup-') as directory:
        program = Path(directory) / 'program.bin'
        program.write_bytes(struct.pack('<4I', 0x13, 0x00408093, 0x6f, 0x007181b3))
        workers = {'bigint', 'blake-g', 'blake-round', 'keccak', 'keccak-column-parity',
                   'keccak-theta-rho', 'keccak-chi5', 'inits-and-teardowns'}
        for expected in paths:
            fresh = Path(directory) / expected.name
            log = Path(directory) / (expected.stem + '.log')
            if expected.stem == 'decoder-smoke':
                command = ['cargo', 'test', '--locked', '-p', 'prover', '--lib',
                           'setup_json_roundtrip_preserves_materialized_columns_and_program']
                export_environment = dict(environment, AIRBENDER_SETUP_JSON_FIXTURE=str(fresh),
                                          CARGO_PROFILE_DEV_DEBUG='0', CARGO_PROFILE_TEST_DEBUG='0',
                                          CARGO_BUILD_JOBS='2')
            else:
                inputs = ['-', '-'] if expected.stem in workers else [str(program), str(program)]
                command = [str(exporter.resolve()), expected.stem, *inputs, str(fresh)]
                export_environment = environment
            with log.open('w') as stream:
                result = subprocess.run(command, cwd=repository, env=export_environment,
                                        stdout=stream, stderr=subprocess.STDOUT)
            if result.returncode:
                raise ValueError(f'Native setup export failed: {expected.stem}; {log.read_text()[-1200:]}')
            compare_artifact(fresh, expected)
            print(f'PASS native setup bytes: {expected.name}', flush=True)
    print(f'PASS {len(paths)} imported native setups')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exporter', type=Path, required=True)
    check(parser.parse_args().exporter)
