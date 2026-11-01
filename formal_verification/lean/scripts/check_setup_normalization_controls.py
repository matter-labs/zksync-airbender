#!/usr/bin/env python3
"""Require kernel rejection of altered setup normalization results."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = '''import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Tests.PackedSetupNormalization
import Airbender.Proofs.GKRProtocol.ShiftPrefixChecks.Column0.Certificate
open Airbender.Compiler.PackedSetupEquality Airbender.Compiler.PackedSetupNormalization
namespace SetupNormalizationControl
'''


def main():
    owner = 'Airbender.Compiler.ShiftPrefixChecks.Column0.'
    controls = [
        ('affine values', 'check Tests.PackedSetupNormalization.requests = true',
         'check [⟨[.affine 2 5 3, .affine 3 12 3], [.affine 5 5 3], 5⟩] = true'),
        ('row counts', 'check Tests.PackedSetupNormalization.requests = true',
         'check [⟨[.affine 2 5 3, .affine 3 11 3], [.affine 5 5 3], 6⟩] = true'),
        ('periodic recipes', 'arrayEqual (.constant 1 3) (.linear 1 3) = true',
         'arrayEqual (.constant 1 3) (.linear 1 4) = true'),
        ('complete capture', f'check {owner}requests = true',
         f'check ({owner}requests ++ [⟨[], [], 1⟩]) = true'),
    ]
    for label, exact, changed in controls:
        for mutated, statement in [(False, exact), (True, changed)]:
            statement = statement.replace('check ', 'Airbender.Compiler.PackedSetupNormalization.check ')
            with tempfile.TemporaryDirectory(prefix='airbender-setup-normalization-') as directory:
                path = Path(directory) / 'Check.lean'
                path.write_text(PREFIX + f'numeric_data_binding result : {statement}\nend SetupNormalizationControl\n')
                result = subprocess.run(['lean', '-j1', '-DElab.async=false', str(path)], cwd=ROOT,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if not mutated and result.returncode:
                raise SystemExit(f'Exact {label} failed:\n' + result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit(f'Changed {label} did not fail in the kernel:\n' + result.stdout[-2000:])
    print('PASS four exact setup normalization controls; kernel rejects all four mutations')


if __name__ == '__main__':
    main()
