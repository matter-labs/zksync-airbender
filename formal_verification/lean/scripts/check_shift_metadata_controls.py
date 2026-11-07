#!/usr/bin/env python3
"""Require exact metadata checks and kernel rejection of altered captures."""
from pathlib import Path
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[1]
PREFIX='''import Airbender.Proofs.Tables.ShiftColumnCoverage
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
open Airbender Airbender.Compiler Airbender.Verification
namespace ShiftMetadataControl
'''


def main():
    owner='Airbender.Verification.ShiftMetadata.'
    checker='FiniteGridChecks.check 7 1 1'
    cases=[
        ('complete offset capture',f'{checker} {owner}offsetsValue (fun _ _ _ => 0) = true',
         f'{checker} {owner}offsetsValue (fun _ _ _ => 1) = true'),
        ('Shift coverage','((byteShiftData.columns[(9 : Nat)]).blocks.toList.map Setup.Block.length).sum = 262144',
         '((byteShiftData.columns[(9 : Nat)]).blocks.toList.map Setup.Block.length).sum = 262143'),
        ('native offset','(shiftData ⟨6, by decide +kernel⟩).offset = 0','(shiftData ⟨6, by decide +kernel⟩).offset = 1'),
        ('binary coverage', '((byteTruncateData.columns[(9 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65536',
         '((byteTruncateData.columns[(9 : Nat)]).blocks.toList.map Setup.Block.length).sum = 65535'),
    ]
    for label,exact,changed in cases:
        for mutated,statement in [(False,exact),(True,changed)]:
            with tempfile.TemporaryDirectory(prefix='airbender-shift-metadata-') as directory:
                path=Path(directory)/'Check.lean'
                path.write_text(PREFIX+f'numeric_data_binding result : {statement}\nend ShiftMetadataControl\n')
                result=subprocess.run(['lean','-j1','-DElab.async=false',str(path)],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            if not mutated and result.returncode:raise SystemExit(f'Exact {label} failed:\n'+result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit(f'Changed {label} did not fail in the kernel:\n'+result.stdout[-2000:])
    print('PASS four exact Shift metadata controls; kernel rejects all four mutations')


if __name__=='__main__':main()
