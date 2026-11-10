#!/usr/bin/env python3
"""Require kernel rejection of altered numeric spans and native bindings."""
from pathlib import Path
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[1]
PREFIX='''import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Tests.PackedSetupSpans
import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.RotateBoundary.Certificate
import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column3.Certificate
import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column5.Certificate
import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column1.Certificate
open Airbender.Compiler.PackedSetupEquality Airbender.Compiler.PackedSetupAccess
open Airbender.Compiler.PackedSetupSpans
namespace SetupSpanControl
'''


def main():
    owner='Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.'
    legacy='Airbender.Compiler.UnifiedPrefixNative.Column1.'
    checker='Airbender.Compiler.PackedSetupSpans.check'
    controls=[
        ('literal getter','arrayGet (.literal 3 197121) 2 = some 3','arrayGet (.literal 3 197121) 2 = some 4'),
        ('packed byte',f'{checker} Tests.PackedSetupSpans.requests = true',f'{checker} [⟨.affine 4 1 1, [.dense (.packedBytes 4 67305986)]⟩] = true'),
        ('source bound','spanCheck (.affine 2 0 1) (.affine 3 0 1) 0 = false','spanCheck (.affine 2 0 1) (.affine 3 0 1) 0 = true'),
        ('complete native spans',f'{checker} {owner}requests = true',f'{checker} ({owner}requests ++ [⟨.affine 1 0 0, []⟩]) = true'),
        ('native source',f'{legacy}source14 = ({owner}sourceCode.get ⟨0, by decide +kernel⟩).decode',f'{legacy}source14 = BlockCode.decode (.affine 262144 0 0)'),
        ('complete native targets',f'{legacy}target14 = {owner}targetsCode.map BlockCode.decode',f'{legacy}target14 = ({owner}targetsCode ++ [BlockCode.affine 0 0 0]).map BlockCode.decode'),
        ('fixed special column five',f'{checker} Airbender.Compiler.UnifiedFixedSpans.Column5.requests = true',
         f'{checker} (Airbender.Compiler.UnifiedFixedSpans.Column5.requests ++ [⟨.affine 1 0 0, []⟩]) = true'),
        ('fixed special column three',f'{checker} Airbender.Compiler.UnifiedFixedSpans.Column3.requests = true',
         f'{checker} (Airbender.Compiler.UnifiedFixedSpans.Column3.requests.map (fun request => {{request with targets := []}})) = true'),
        ('complete fixed column one',f'{checker} Airbender.Compiler.UnifiedFixedSpans.Column1.requests = true',
         f'{checker} (Airbender.Compiler.UnifiedFixedSpans.Column1.requests ++ [⟨.affine 1 0 0, []⟩]) = true'),
        ('fixed column one source',f'{legacy}source0 = (Airbender.Compiler.UnifiedFixedSpans.Column1.source0.get ⟨0, by decide +kernel⟩).decode',
         f'{legacy}source0 = BlockCode.decode (.affine 1 1 0)'),
    ]
    for label,exact,changed in controls:
        for mutated,statement in [(False,exact),(True,changed)]:
            with tempfile.TemporaryDirectory(prefix='airbender-setup-span-') as directory:
                path=Path(directory)/'Check.lean'
                path.write_text(PREFIX+f'numeric_data_binding result : {statement}\nend SetupSpanControl\n')
                result=subprocess.run(['lean','-j1','-DElab.async=false',str(path)],cwd=ROOT,
                                      stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            if not mutated and result.returncode:
                raise SystemExit(f'Exact {label} failed:\n'+result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit(f'Changed {label} did not fail in the kernel:\n'+result.stdout[-2000:])
    print('PASS ten exact numeric span and native binding controls; kernel rejects all ten mutations')


if __name__=='__main__':main()
