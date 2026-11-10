#!/usr/bin/env python3
"""Require complete length checks and exact source bindings in the kernel."""
from pathlib import Path
import subprocess
import tempfile
from gkr_packed_region_lengths import metadata_plan

ROOT=Path(__file__).resolve().parents[1]
PREFIX='''import Tests.PackedSetupLengths
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
import Airbender.Proofs.GKRProtocol.UnifiedRegionLengths.Column1.Certificate
import Airbender.Proofs.GKRProtocol.UnifiedRegionLengths.Column3.Certificate
import Airbender.Proofs.GKRProtocol.UnifiedRegionLengths.Column5.Certificate
import Airbender.Proofs.GKRProtocol.UnifiedRegionLengths.Column8.Certificate
open Airbender Airbender.Compiler PackedSetupEquality
namespace SetupLengthControl
'''


def main():
    checker='PackedSetupLengths.check'
    cases=[('numeric recipes',f'{checker} Tests.PackedSetupLengths.requests = true',
            f'{checker} (Tests.PackedSetupLengths.requests ++ [⟨[], 1⟩]) = true')]
    for column in [1,3,5,8]:
        requests=f'Airbender.Compiler.UnifiedRegionLengths.Column{column}.requests'
        cases.append((f'complete column {column}',f'{checker} {requests} = true',f'{checker} ({requests} ++ [⟨[], 1⟩]) = true'))
    for column,kind in [(1,'known'),(3,'known'),(5,'equal'),(8,'extra')]:
        ordinal,entry=next((index,entry) for index,entry in enumerate(metadata_plan(column)) if entry['kind']==kind)
        view=f'Airbender.Compiler.UnifiedRegionLengths.Column{column}.view{ordinal}'
        cases.append((f'column {column} {kind} binding',f'{entry["piece"]} = {view}.map BlockCode.decode',
                      f'{entry["piece"]} = ({view} ++ [BlockCode.affine 0 0 0]).map BlockCode.decode'))
    for label,exact,changed in cases:
        for mutated,statement in [(False,exact),(True,changed)]:
            with tempfile.TemporaryDirectory(prefix='airbender-setup-length-') as directory:
                path=Path(directory)/'Check.lean'
                path.write_text(PREFIX+f'numeric_data_binding result : {statement}\nend SetupLengthControl\n')
                result=subprocess.run(['lean','-j1','-DElab.async=false',str(path)],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            if not mutated and result.returncode:raise SystemExit(f'Exact {label} failed:\n'+result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit(f'Changed {label} did not fail in the kernel:\n'+result.stdout[-2000:])
    print(f'PASS {len(cases)} exact setup length controls; kernel rejects all {len(cases)} mutations')


if __name__=='__main__':main()
