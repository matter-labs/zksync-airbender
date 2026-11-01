#!/usr/bin/env python3
"""Check every functional port class and reject changed native source windows."""
from pathlib import Path
import argparse
import subprocess
import tempfile

from gkr_packed_functional_steps import CASES, capture

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import Airbender.Proofs.GKRProtocol.NumericFunctionalStepChecks
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
open Airbender.Compiler NumericFunctionalStepChecks
namespace FunctionalStepControl
set_option maxRecDepth 8192
def first : Data := ⟨[], [(20, 0)], [(10, 1)]⟩
def second : Data := ⟨[], [(30, 0)], [(20, 0)]⟩
def tiny : List Data := [first, second]
'''


def run(source):
    with tempfile.TemporaryDirectory(prefix='airbender-functional-step-') as directory:
        path = Path(directory) / 'Check.lean'
        path.write_text(source)
        return subprocess.run(['lean', '--tstack=32768', '-j1', '-DElab.async=false', str(path)],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', choices=CASES, action='append')
    args = parser.parse_args()
    changes = [
        ('unique outputs', '[{first with outputs := [(20,0),(20,0)]}, second]'),
        ('fresh output', '[first, {second with outputs := [(20,0)]}]'),
        ('base output', '[{first with outputs := [(20,1)]}, second]'),
        ('invalid output flag', '[{first with outputs := [(20,2)]}, second]'),
        ('unknown input', '[first, {second with inputs := [(99,0)]}]'),
        ('missing base input', '[{first with inputs := [(10,0)]}, second]')]
    cases = [(label, 'treeCheck ∅ tiny = true', f'treeCheck ∅ {changed} = true', '')
             for label, changed in changes]
    if args.case:
        cases = []
    for case in args.case or CASES:
        owner = 'Airbender.Compiler.FunctionalStepChecks.' + case
        native = 'Airbender.Compiler.FunctionalNative.' + case + '.native'
        imports = f'import Airbender.Proofs.GKRProtocol.FunctionalStepChecks.{case}.Certificate\n'
        count = len(capture(case))
        for first in [0, (count - 1) // 8 * 8]:
            width = min(8, count - first)
            base, offset = first // 32 * 32, first % 32
            values = f'({owner}.ports{base}.drop {offset}).take {width}'
            expected = f'(({native}.program.drop {first}).take {width}).map {owner}.encodePort'
            cases.append((case + f' window {first}', f'{values} = {expected}', f'({values}).drop 1 = {expected}', imports))
    for label, exact, changed, imports in cases:
        for mutated, statement in [(False, exact), (True, changed)]:
            result = run(imports + PREFIX + f'numeric_data_binding result : {statement}\nend FunctionalStepControl\n')
            if not mutated and result.returncode:
                raise SystemExit(f'Exact {label} failed:\n' + result.stdout[-2500:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit(f'Changed {label} did not fail in the kernel:\n' + result.stdout[-2500:])
        print('PASS functional-step control:', label, flush=True)
    if not args.case:
        result = run('''import Airbender.Import.GKRProtocol.NumericFunctionalStepImport
open Airbender.Compiler
opaque hidden : List NumericFunctionalStepChecks.Data := []
numeric_functional_steps_capture rejected := hidden
''')
        if not result.returncode or 'did not reduce to closed numeric data' not in result.stdout:
            raise SystemExit('Opaque functional ports were not rejected:\n' + result.stdout[-2500:])
    print(f'PASS {len(cases)} exact controls; kernel rejects all {len(cases)} mutations')
    if not args.case:
        print('PASS opaque functional port rejection')


if __name__ == '__main__':
    main()
