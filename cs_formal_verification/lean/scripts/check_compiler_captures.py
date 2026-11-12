#!/usr/bin/env python3
"""Check pinned cached compiler captures and their production artifact bindings."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent.parent
sys.path.insert(0, str(ROOT))
from check_circuit_json import reject_duplicates, reject_constant

FAMILIES = {
    'add-sub': 'add_sub_lui_auipc_mop', 'bigint': 'bigint_with_extended_control',
    'blake-g': 'blake2_g_function', 'blake-round': 'blake2_with_extended_control',
    'jump-branch': 'jump_branch_slt', 'keccak': 'keccak_special5', 'mul-div': 'unsigned_mul_div',
    'shift-binop': 'shift_binop', 'subword-memory': 'mem_subword_only',
    'unified': 'unified_reduced_machine', 'word-memory': 'mem_word_only',
}


def read(path):
    return json.loads(path.read_bytes(), object_pairs_hook=reject_duplicates, parse_constant=reject_constant)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)


def check():
    pins = read(ROOT / 'compiler_capture_pins.json')
    expected = {f'artifacts/compiler/{family}-cached{suffix}.json'
                for family in FAMILIES for suffix in ('', '-source')}
    inputs = set(re.findall(r'"(artifacts/compiler/[A-Za-z0-9_.-]+\.json)"',
                            (ROOT / 'lakefile.toml').read_text()))
    if set(pins) != expected or inputs != expected:
        raise ValueError('Compiler pin and Lake input inventories must cover all 11 cached captures and sidecars')
    for name, digest in pins.items():
        path = ROOT / name
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f'Compiler capture bytes changed: {name}')
        read(path)
    for family, circuit in FAMILIES.items():
        capture = read(ROOT / f'artifacts/compiler/{family}-cached.json')
        source = read(ROOT / f'artifacts/compiler/{family}-cached-source.json')
        if (capture['format_version'] != 1 or capture['cached'] is not True or capture['family'] != family or
                source['format_version'] != 1 or source['cached'] is not True or source['family'] != family):
            raise ValueError(f'Compiler capture profile differs: {family}')
        if canonical(capture['source']) != canonical(source['source']):
            raise ValueError(f'Compiler source snapshot differs from its sidecar: {family}')
        native = read(REPO / f'cs/compiled_circuits/{circuit}_layout_gkr.json')
        if canonical(capture['circuit']) != canonical(native):
            raise ValueError(f'Compiler capture differs from the production cached artifact: {family}')
    sys.set_int_max_str_digits(100000)
    certificate_pins = read(ROOT / 'compiler_certificate_pins.json')
    certificate_paths = {str(path.relative_to(ROOT))
                         for directory in ('numeric-arithmetic', 'numeric-clean')
                         for path in (ROOT / 'artifacts/compiler' / directory).glob('*.json')}
    if set(certificate_pins) != certificate_paths:
        raise ValueError('Compiler certificate pins do not cover every numeric payload')
    for name, digest in certificate_pins.items():
        path = ROOT / name
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f'Compiler certificate bytes changed: {name}')
        read(path)
    print('PASS 11 pinned cached compiler captures, source sidecars and numeric certificates')


def fresh(exporter):
    with tempfile.TemporaryDirectory(prefix='airbender-compiler-') as directory:
        for family in FAMILIES:
            output = Path(directory) / f'{family}-cached.json'
            log = Path(directory) / f'{family}.log'
            with log.open('w') as stream:
                result = subprocess.run([str(exporter.resolve()), family, str(output), '--cached'],
                                        env=dict(os.environ, RAYON_NUM_THREADS='1'),
                                        stdout=stream, stderr=subprocess.STDOUT)
            if result.returncode:
                raise ValueError(f'Compiler export failed: {family}; {log.read_text()[-1200:]}')
            for path in (output, output.with_name(output.stem + '-source.json')):
                if path.read_bytes() != (ROOT / 'artifacts/compiler' / path.name).read_bytes():
                    raise ValueError(f'Fresh compiler export differs: {path.name}')
            print(f'PASS fresh cached compiler bytes: {family}', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exporter', type=Path)
    args = parser.parse_args()
    check()
    if args.exporter:
        fresh(args.exporter)
