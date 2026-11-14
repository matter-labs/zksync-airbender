#!/usr/bin/env python3
"""Run precompiled exact Miri cases concurrently; keep case logs and timing summary."""
import argparse
import concurrent.futures
import pathlib
import re
import subprocess
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--package', required=True)
parser.add_argument('--features', required=True)
parser.add_argument('--test-target', required=True)
parser.add_argument('--cases', nargs='+', required=True)
parser.add_argument('--output', type=pathlib.Path, required=True)
parser.add_argument('--jobs', type=int, required=True)
parser.add_argument('--case-config', nargs=3, action='append', default=[],
                    metavar=('CASE', 'FEATURES', 'TEST_TARGET'))
args = parser.parse_args()
cases = args.cases
assert args.jobs > 0 and cases
case_configs = {case: (features, target) for case, features, target in args.case_config}
assert len(case_configs) == len(args.case_config) and set(case_configs) <= set(cases)
args.output.mkdir(parents=True, exist_ok=True)

def run(case):
    started = time.monotonic()
    log = args.output / (case + '.log')
    features, target = case_configs.get(case, (args.features, args.test_target))
    command = ['cargo', 'miri', 'test', '-p', args.package, '--no-default-features',
               '--features', features, '--test', target,
               '--', '--exact', case]
    with log.open('w') as output:
        exit_code = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT).returncode
    text = log.read_text()
    positive = bool(re.search(r'test result: ok\. 1 passed; 0 failed;', text))
    rebuilt = bool(re.search(r'^\s*(Compiling|Checking) ', text, re.MULTILINE))
    return {'test': case, 'wall_seconds': time.monotonic() - started,
            'exit_code': exit_code, 'one_test_passed': positive,
            'unexpected_compile': rebuilt, 'passed': exit_code == 0 and positive and not rebuilt}

with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
    results = []
    for future in concurrent.futures.as_completed([pool.submit(run, case) for case in cases]):
        result = future.result()
        results.append(result)
        if not result['passed']:
            print('\n'.join((args.output / (result['test'] + '.log')).read_text().splitlines()[-40:]), flush=True)
        print(f"{result['test']}: {'PASS' if result['passed'] else 'FAIL'} "
              f"{result['wall_seconds']:.2f}s exit={result['exit_code']}", flush=True)
results.sort(key=lambda row: row['test'])
lines = ['| Miri case | Wall seconds | Result | Exit | One test passed | Unexpected compile |', '|---|---:|---|---:|---|---|']
for result in results:
    status = 'PASS' if result['passed'] else 'FAIL'
    lines.append(f"| `{result['test']}` | {result['wall_seconds']:.2f} | {status} | {result['exit_code']} | {result['one_test_passed']} | {result['unexpected_compile']} |")
(args.output / 'summary.md').write_text('\n'.join(lines) + '\n')
raise SystemExit(0 if all(result['passed'] for result in results) else 1)
