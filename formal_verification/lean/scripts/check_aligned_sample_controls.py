#!/usr/bin/env python3
"""Require complete aligned samples and exact native block bindings."""
from pathlib import Path
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[1]
PREFIX='''import Airbender.Proofs.Tables.AlignedSampleChecks.Certificate
open Airbender Airbender.Compiler Airbender.Verification PackedSetupEquality
namespace AlignedSampleControl
'''


def main():
    checker='PackedSetupSamples.check'
    exact=f'{checker} [⟨[BlockCode.affine 32768 7 0], 1, fun _ => 7⟩] = true'
    cases=[
        ('zero stride',exact,f'{checker} [⟨[BlockCode.affine 32768 7 1], 1, fun _ => 7⟩] = true'),
        ('alignment',exact,f'{checker} [⟨[BlockCode.affine 32767 7 0], 1, fun _ => 7⟩] = true'),
        ('sample value',exact,f'{checker} [⟨[BlockCode.affine 32768 7 0], 1, fun _ => 8⟩] = true'),
        ('empty extent',f'{checker} [⟨[], 0, fun i => Fin.elim0 i⟩] = true',
         f'{checker} [⟨[], 1, fun _ => 0⟩] = true'),
    ]
    for name,original in [('conditional','(conditionalData.columns[1]).blocks.toList'),('position','byteShiftColumn0.blocks.toList')]:
        owner=f'AlignedSampleChecks.{name}'
        cases.append((name,f'{checker} {owner}Requests = true',
                      f'{checker} ({owner}Requests ++ [⟨[BlockCode.affine 1 0 0], 0, fun i => Fin.elim0 i⟩]) = true'))
        cases.append((name+' binding',f'{original} = {owner}Blocks.map BlockCode.decode',
                      f'{original} = ({owner}Blocks ++ [BlockCode.affine 0 0 0]).map BlockCode.decode'))
    for label,exact,changed in cases:
        for mutated,statement in [(False,exact),(True,changed)]:
            with tempfile.TemporaryDirectory(prefix='airbender-aligned-samples-') as directory:
                path=Path(directory)/'Check.lean';path.write_text(PREFIX+f'numeric_data_binding result : {statement}\nend AlignedSampleControl\n')
                result=subprocess.run(['lean','-j1','-DElab.async=false',str(path)],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            if not mutated and result.returncode:raise SystemExit(f'Exact {label} failed:\n'+result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit(f'Changed {label} did not fail in the kernel:\n'+result.stdout[-2000:])
    print(f'PASS {len(cases)} exact aligned sample controls; kernel rejects all {len(cases)} mutations')


if __name__=='__main__':main()
