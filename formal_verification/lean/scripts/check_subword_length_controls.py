#!/usr/bin/env python3
"""Require complete fixed Subword lengths and exact import bindings."""
from pathlib import Path
import subprocess
import tempfile
from gkr_packed_subword_lengths import metadata_plan

ROOT=Path(__file__).resolve().parents[1]
PREFIX='''import Airbender.Proofs.GKRProtocol.SubwordRegionLengths.Column1.Certificate
import Airbender.Proofs.GKRProtocol.SubwordRegionLengths.Column2.Certificate
import Airbender.Proofs.GKRProtocol.SubwordRegionLengths.Column8.Certificate
open Airbender Airbender.Compiler PackedSetupEquality
namespace SubwordLengthControl
'''


def main():
    checker='PackedSetupLengths.check'
    cases=[('signed block length',f'{checker} [⟨[BlockCode.affine 4 7 (-1)], 4⟩] = true',
            f'{checker} [⟨[BlockCode.affine 4 7 (-1)], 5⟩] = true')]
    for column in [1,2,8]:
        requests=f'Airbender.Compiler.SubwordRegionLengths.Column{column}.requests'
        cases.append((f'complete column {column}',f'{checker} {requests} = true',f'{checker} ({requests} ++ [⟨[], 1⟩]) = true'))
    for column in [1,8]:
        entry=metadata_plan(column)[4];view=f'Airbender.Compiler.SubwordRegionLengths.Column{column}.region4'
        original=entry['source']+'.blocks.toList'
        cases.append((f'fixed column {column} binding',f'{original} = {view}.map BlockCode.decode',
                      f'{original} = ({view} ++ [BlockCode.affine 0 0 0]).map BlockCode.decode'))
    for label,exact,changed in cases:
        for mutated,statement in [(False,exact),(True,changed)]:
            with tempfile.TemporaryDirectory(prefix='airbender-subword-length-') as directory:
                path=Path(directory)/'Check.lean'
                path.write_text(PREFIX+f'numeric_data_binding result : {statement}\nend SubwordLengthControl\n')
                result=subprocess.run(['lean','-j1','-DElab.async=false',str(path)],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            if not mutated and result.returncode:raise SystemExit(f'Exact {label} failed:\n'+result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit(f'Changed {label} did not fail in the kernel:\n'+result.stdout[-2000:])
    print(f'PASS {len(cases)} exact Subword length controls; kernel rejects all {len(cases)} mutations')


if __name__=='__main__':main()
