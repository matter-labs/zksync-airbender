#!/usr/bin/env python3
"""Replay and audit exactly the registered compiler-preservation roots.

Run inside bounded_fv.py. Imports build sequentially through normal Lake
invalidation. Reports are checked against the exact registered name inventory.
"""
import argparse
import os
from pathlib import Path
import re
import subprocess
import tempfile

from export_gkr_translations import LEAN

EXPECTED_ROOTS = 6955
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
MARKER = '-- GKR compiler translation validation.'
REPORT = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$", re.M)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log', type=Path, default=Path('/tmp/gkr-compiler-axioms.log'))
    args = parser.parse_args()
    registry = (LEAN / 'Airbender/Checks/Axioms.lean').read_text()
    if registry.count(MARKER) != 1:
        raise ValueError('compiler audit marker changed')
    roots = [line.removeprefix('#print axioms ') for line in registry.split(MARKER)[1].splitlines()
             if line.startswith('#print axioms ')]
    if len(roots) != len(set(roots)) or len(roots) != EXPECTED_ROOTS:
        raise ValueError(f'compiler root inventory changed: {len(roots)}, expected {EXPECTED_ROOTS}')
    modules = list(dict.fromkeys(line.removeprefix('import ') for line in registry.splitlines()
                                if line.startswith(('import GKR', 'import Tests.GKR'))))
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
    print(f'PASS exact {len(reports)} compiler roots; standard Lean axioms only', flush=True)


if __name__ == '__main__':
    main()
