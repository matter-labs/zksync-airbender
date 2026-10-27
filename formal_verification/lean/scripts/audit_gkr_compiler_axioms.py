#!/usr/bin/env python3
"""Check compiler roots against an environment audit, or run a direct smoke test.

Run inside bounded_fv.py. Imports build sequentially through normal Lake
invalidation. Reports are checked against the exact registered name inventory.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from export_gkr_translations import LEAN

ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
MARKER = '-- GKR compiler translation validation.'
REPORT = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$", re.M)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log', type=Path, default=Path('/tmp/gkr-compiler-axioms.log'))
    parser.add_argument('--axiom-result', type=Path,
                        help='Authoritative check_axioms.py result; otherwise only a direct smoke test')
    args = parser.parse_args()
    registry = (LEAN / 'Airbender/Checks/Axioms.lean').read_text()
    if registry.count(MARKER) != 1:
        raise ValueError('compiler audit marker changed')
    roots = [line.removeprefix('#print axioms ') for line in registry.split(MARKER)[1].splitlines()
             if line.startswith('#print axioms ')]
    if not roots or len(roots) != len(set(roots)):
        raise ValueError('empty or duplicate compiler root inventory')
    if args.axiom_result:
        result = json.loads(args.axiom_result.read_text())
        if (result.get('schema') != 'airbender-axiom-result-v1' or not result.get('passed')
                or not result.get('compiled_environment_only')
                or set(roots) - result.get('roots', {}).keys()
                or any(set(result.get('axioms', {}).get(name, ['missing'])) - ALLOWED_AXIOMS for name in roots)):
            raise ValueError('compiler roots lack a complete passing environment-origin audit')
        print(f'PASS {len(roots)} compiler roots in the environment-origin audit', flush=True)
        return
    modules = list(dict.fromkeys(line.removeprefix('import ') for line in registry.splitlines()
                                if line.startswith(('import Airbender.Proofs.GKR', 'import Airbender.Import.GKR', 'import Airbender.Review.Compiler.', 'import Tests.GKR'))))
    environment = dict(os.environ, LEAN_NUM_THREADS='1')
    for module in modules:
        subprocess.run(['lake', '--no-cache', 'build', '+' + module + ':olean'],
                       cwd=LEAN, env=environment, check=True)
    args.log.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='gkr-axiom-audit-') as directory:
        source = Path(directory) / 'CompilerAxioms.lean'
        source.write_text(''.join('import ' + module + '\n' for module in modules) +
                          ''.join('#print axioms ' + root + '\n' for root in roots))
        with args.log.open('w') as output:
            subprocess.run(['lake', 'env', 'lean', str(source)], cwd=LEAN, env=environment,
                           stdout=output, stderr=subprocess.STDOUT, check=True)
    reports = REPORT.findall(args.log.read_text())
    if len(reports) != len(roots) or {name for name, _ in reports} != set(roots):
        raise ValueError('axiom reports do not match the exact registered compiler roots')
    for name, axioms in reports:
        actual = set(filter(None, map(str.strip, axioms.split(','))))
        if not actual <= ALLOWED_AXIOMS:
            raise ValueError(f'unexpected compiler axiom: {name}: {sorted(actual)}')
    print(f'PASS direct smoke test for {len(reports)} compiler roots; '
          'constructor-field dependencies require the separate environment-origin audit', flush=True)


if __name__ == '__main__':
    main()
