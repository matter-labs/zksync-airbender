#!/usr/bin/env python3
"""Regenerate every imported compiled circuit with its Rust generator test and compare it with the committed file.

The generator tests skip when the environment contains CI (`skip_if_ci!` tests presence, so CI=false also skips).
This script runs each test with CI removed and requires that the test passes and rewrites its file.
It restores the affected artifact directories after the comparison.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = ROOT.parent.parent
sys.path.insert(0, str(ROOT))
from check_circuit_json import imported_paths, load
from check_compiler_captures import CIRCUIT_CRATES, cached_layout

# No-cache layouts still come from the compiler tests in cs.
NO_CACHE_GENERATORS = {
    'add_sub_lui_auipc_mop_layout_no_caches_gkr.json':
        'gkr_circuits::add_sub_family::circuit::test::compile_add_sub_lui_auipc_mop_into_no_caches_gkr',
    'jump_branch_slt_layout_no_caches_gkr.json':
        'gkr_circuits::jump_branch_slt_family::circuit::test::compile_jump_branch_slt_circuit_into_no_caches_gkr',
    'unsigned_mul_div_layout_no_caches_gkr.json':
        'gkr_circuits::mul_div::circuit::test::compile_unsigned_mul_div_into_no_caches_gkr',
    'shift_binop_layout_no_caches_gkr.json':
        'gkr_circuits::binary_shifts_family::circuit::test::compile_shift_binop_into_no_caches_gkr',
    'mem_word_only_layout_no_caches_gkr.json':
        'gkr_circuits::mem_word_only::circuit::test::compile_mem_word_only_circuit_into_no_caches_gkr',
    'mem_subword_only_layout_no_caches_gkr.json':
        'gkr_circuits::mem_subword_only::circuit::test::compile_mem_subword_only_circuit_into_no_caches_gkr',
    'unified_reduced_machine_layout_no_caches_gkr.json':
        'gkr_circuits::unified_reduced_machine::circuit::test::compile_unified_reduced_machine_into_no_caches_gkr',
    'bigint_with_extended_control_layout_no_caches_gkr.json':
        'gkr_circuits::delegation::bigint_with_control::test::compile_bigint_with_extended_control_into_no_caches_gkr',
    'blake2_g_function_layout_no_caches_gkr.json':
        'gkr_circuits::delegation::blake2_g_function::test::compile_blake2_g_function_into_no_caches_gkr',
    'blake2_with_extended_control_layout_no_caches_gkr.json':
        'gkr_circuits::delegation::blake2_round_with_extended_control::test::compile_blake2_with_extended_control_into_no_caches_gkr',
    'keccak_special5_layout_no_caches_gkr.json':
        'gkr_circuits::delegation::keccak_special5::test::compile_keccak_special5_into_no_caches_gkr',
    'keccak_column_parity_layout_no_caches_gkr.json':
        'gkr_circuits::delegation::keccak_f1600_artifacts::compile_keccak_column_parity_into_no_caches_gkr',
    'keccak_theta_rho_layout_no_caches_gkr.json':
        'gkr_circuits::delegation::keccak_f1600_artifacts::compile_keccak_theta_rho_into_no_caches_gkr',
    'keccak_chi5_layout_no_caches_gkr.json':
        'gkr_circuits::delegation::keccak_f1600_artifacts::compile_keccak_chi5_into_no_caches_gkr',
    'inits_and_teardowns_layout_no_caches_gkr.json':
        'gkr_compiler::inits_and_teardowns::test::compile_inits_and_teardowns_into_no_caches_gkr',
}

# Each cached layout comes from the owning circuit crate.
GENERATORS = {
    f'cs/compiled_circuits/{name}': ('cs', test)
    for name, test in NO_CACHE_GENERATORS.items()
}
for stem in CIRCUIT_CRATES:
    layout = cached_layout(stem)
    GENERATORS[layout.relative_to(REPOSITORY).as_posix()] = (layout.parents[1].name, 'test::generate')


def generator_tests(names):
    """The generator tests for the named files, each once, in first-use order. Fail on an unmapped file."""
    unmapped = sorted(set(names) - set(GENERATORS))
    if unmapped:
        raise ValueError('Imported circuit without a generator test: ' + ', '.join(unmapped))
    return list(dict.fromkeys(GENERATORS[name] for name in names))


def compare_circuit(name, fresh, committed):
    """The canonical form of the regenerated value is the committed file, byte for byte."""
    canonical = json.dumps(load(fresh), indent=2).encode()
    if canonical != committed:
        raise ValueError(f'Regenerated circuit differs from the committed file: {name}')


def run_generators(tests, environment, directory):
    tests_by_package = {}
    for package, test in tests:
        tests_by_package.setdefault(package, []).append(test)
    for package, selectors in tests_by_package.items():
        command = ['cargo', 'test', '--profile', 'cli', '-p', package, '--lib', '--',
                   '--exact', '--nocapture', '--test-threads=1', *selectors]
        log = directory / f'{package}.log'
        with log.open('w') as stream:
            result = subprocess.run(command, cwd=REPOSITORY, env=environment, stdout=stream, stderr=subprocess.STDOUT)
        output = log.read_text()
        if result.returncode:
            raise ValueError(f'Generator tests failed for {package}; {output[-2000:]}')
        check_test_output(output, len(selectors))


def check_test_output(output, count):
    """Every selected test ran, and no test returned early through `skip_if_ci!`."""
    if f'test result: ok. {count} passed' not in output or 'skipping' in output:
        raise ValueError(f'Generator tests did not all run; {output[-2000:]}')


def modified(path):
    status = path.stat()
    return status.st_mtime_ns, status.st_ctime_ns


def check(names):
    environment = {key: value for key, value in os.environ.items() if key != 'CI'}
    environment['RAYON_NUM_THREADS'] = '1'
    tests = generator_tests(names)
    paths = {name: REPOSITORY / name for name in names}
    artifact_dirs = {path.parent for path in paths.values()}
    committed = {path: path.read_bytes() for directory in artifact_dirs
                 for path in directory.iterdir() if path.is_file()}
    before = {name: modified(path) for name, path in paths.items()}
    try:
        with tempfile.TemporaryDirectory(prefix='airbender-circuits-') as directory:
            run_generators(tests, environment, Path(directory))
        print(f'PASS {len(tests)} generator tests ran', flush=True)
        for name, fresh in paths.items():
            if modified(fresh) == before[name]:
                raise ValueError(f'Generator test did not rewrite its circuit: {name}')
            compare_circuit(name, fresh.read_bytes(), committed[fresh])
            print(f'PASS regenerated circuit: {name}', flush=True)
    finally:
        for directory in artifact_dirs:
            for path in directory.iterdir():
                if path.is_file() and path not in committed:
                    path.unlink()
        for path, data in committed.items():
            if not path.is_file() or path.read_bytes() != data:
                path.write_bytes(data)

    print(f'PASS {len(names)} imported circuits regenerated by {len(tests)} generator tests')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only', nargs='+', metavar='FILE',
                        help='check only these imported repo-relative paths (for a local subset run)')
    args = parser.parse_args()
    imported = [path.relative_to(REPOSITORY).as_posix() for path in imported_paths()]
    if set(GENERATORS) != set(imported):
        stale = sorted(set(GENERATORS) - set(imported))
        missing = sorted(set(imported) - set(GENERATORS))
        raise ValueError(f'Generator inventory differs from the imported circuits. Missing: {missing}. Stale: {stale}')
    # Preserve basename selectors for the no-cache files.
    names = [f'cs/compiled_circuits/{name}' if name in NO_CACHE_GENERATORS else name
             for name in args.only] if args.only else imported
    if not set(names) <= set(imported):
        raise ValueError('Not an imported circuit: ' + ', '.join(sorted(set(names) - set(imported))))
    check(names)


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError) as error:
        raise SystemExit('FAIL ' + str(error))
