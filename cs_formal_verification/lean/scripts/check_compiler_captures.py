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
from check_circuit_json import reject_duplicates, reject_constant, imported_paths, setup_paths

FAMILIES = {
    'add-sub': 'add_sub_lui_auipc_mop', 'bigint': 'bigint_with_extended_control',
    'blake-g': 'blake2_g_function', 'blake-round': 'blake2_with_extended_control',
    'jump-branch': 'jump_branch_slt', 'keccak': 'keccak_special5', 'mul-div': 'unsigned_mul_div',
    'shift-binop': 'shift_binop', 'subword-memory': 'mem_subword_only',
    'unified': 'unified_reduced_machine', 'word-memory': 'mem_word_only',
    'keccak-column-parity': 'keccak_column_parity', 'keccak-theta-rho': 'keccak_theta_rho',
    'keccak-chi5': 'keccak_chi5',
}


CIRCUIT_CRATES = {
    'add_sub_lui_auipc_mop': 'unrolled_circuits/add_sub_lui_auipc_mop',
    'bigint_with_extended_control': 'bigint_with_control',
    'blake2_g_function': 'blake2_g_function',
    'blake2_with_extended_control': 'blake2_with_compression',
    'inits_and_teardowns': 'unrolled_circuits/inits_and_teardowns',
    'jump_branch_slt': 'unrolled_circuits/jump_branch_slt',
    'keccak_chi5': 'keccak_chi5',
    'keccak_column_parity': 'keccak_column_parity',
    'keccak_special5': 'keccak_special5',
    'keccak_theta_rho': 'keccak_theta_rho',
    'mem_subword_only': 'unrolled_circuits/load_store_subword_only',
    'mem_word_only': 'unrolled_circuits/load_store_word_only',
    'shift_binop': 'unrolled_circuits/shift_binary',
    'unified_reduced_machine': 'unrolled_circuits/unified_reduced_machine',
    'unsigned_mul_div': 'unrolled_circuits/mul_div_unsigned',
}


def cached_layout(stem):
    return REPO / 'circuit_defs' / CIRCUIT_CRATES[stem] / 'generated/layout.json'


def read(path):
    return json.loads(path.read_bytes(), object_pairs_hook=reject_duplicates, parse_constant=reject_constant)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)


def check_setup_pins():
    pins = read(ROOT / 'setup_json_pins.json')
    paths = setup_paths()
    expected = {str(path.relative_to(ROOT)) for path in paths}
    if set(pins) != expected:
        raise ValueError('Setup pins must cover every imported setup JSON')
    for name, digest in pins.items():
        if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != digest:
            raise ValueError(f'Setup bytes changed: {name}')
    table = (ROOT / 'artifacts/setup/README.md').read_text()
    for name, digest in re.findall(r'\| `([^`]+\.json)` \| `([0-9a-f]{64})` \|', table):
        if pins.get('artifacts/setup/' + name) != digest:
            raise ValueError(f'Setup README hash differs from its pin: {name}')
    print(f'PASS {len(paths)} setup content pins and README hashes')


# The derived decoder fixture embeds a test circuit, not a production circuit.
SETUP_FIXTURES = {'decoder-smoke'}


def check_setup_circuits():
    """Each production setup embeds the imported no-cache circuit of its family."""
    imported = {path.name: path for path in imported_paths()}
    families = dict(FAMILIES, **{'inits-and-teardowns': 'inits_and_teardowns'})
    checked = 0
    for path in setup_paths():
        if path.stem in SETUP_FIXTURES:
            continue
        if path.stem not in families:
            raise ValueError(f'Setup without a production circuit family: {path.name}')
        circuit = imported.get(families[path.stem] + '_layout_no_caches_gkr.json')
        if circuit is None:
            raise ValueError(f'Setup family has no imported no-cache circuit: {path.name}')
        if canonical(read(path)['circuit']) != canonical(read(circuit)):
            raise ValueError(f'Setup embeds a different circuit than the imported no-cache file: {path.name}')
        checked += 1
    print(f'PASS {checked} setups embed their imported no-cache circuits')


def check_cached_layouts():
    suffix = '_layout_no_caches_gkr.json'
    checked = 0
    for path in imported_paths():
        if not path.name.endswith(suffix):
            continue
        name = path.name[:-len(suffix)]
        cached = read(cached_layout(name))
        plain = read(path)
        cached.pop('layers')
        plain.pop('layers')
        if canonical(cached) != canonical(plain):
            raise ValueError(f'Cached constraint description differs from no-cache layout: {name}')
        checked += 1
    print(f'PASS {checked} complete cached/no-cache constraint descriptions')


def check():
    check_setup_pins()
    check_setup_circuits()
    check_cached_layouts()
    pins = read(ROOT / 'compiler_capture_pins.json')
    expected = {f'artifacts/compiler/{family}-cached{suffix}.json'
                for family in FAMILIES for suffix in ('', '-source')}
    inputs = set(re.findall(r'"(artifacts/compiler/[A-Za-z0-9_.-]+\.json)"',
                            (ROOT / 'lakefile.toml').read_text()))
    if set(pins) != expected or inputs != expected:
        raise ValueError('Compiler pin and Lake input inventories must cover all cached captures and sidecars')
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
        if set(capture) != {'format_version', 'cached', 'family', 'source'}:
            raise ValueError(f'Source capture contains fields outside its source snapshot: {family}')
        expected_path = f'../../{cached_layout(circuit).relative_to(REPO).as_posix()}'
        readers = [path for path in (ROOT / 'human/Human/Compiler/Captures').glob('*.lean')
                   if f'family := "{family}"' in path.read_text()]
        if len(readers) != 1 or f'import_circuit importedCircuit from "{expected_path}" shared imported' not in readers[0].read_text():
            raise ValueError(f'Cached circuit must use the proved importer: {family}')
    sys.set_int_max_str_digits(100000)
    certificate_pins = read(ROOT / 'compiler_certificate_pins.json')
    certificate_root = ROOT / 'artifacts/compiler'
    certificate_paths = {str(path.relative_to(ROOT))
                         for path in certificate_root.rglob('*.json') if path.parent != certificate_root}
    if set(certificate_pins) != certificate_paths:
        raise ValueError('Compiler certificate pins do not cover every arithmetic and lookup payload')
    for name, digest in certificate_pins.items():
        path = ROOT / name
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f'Compiler certificate bytes changed: {name}')
        read(path)
    print(f'PASS {len(FAMILIES)} pinned source captures, sidecars and arithmetic/lookup certificates')


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
