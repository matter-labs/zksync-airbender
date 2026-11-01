#!/usr/bin/env python3
"""Require exact sample checks and reject changed arrays in the kernel."""
from pathlib import Path
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[1]
PREFIX='''import Airbender.Proofs.Tables.SubwordSampleBindings
import Airbender.Proofs.Tables.ShiftSampleBindings
open Airbender.Verification
open ArraySampleChecks
namespace ArraySampleControl
'''


def main():
    cases=[
        ('empty','check [⟨0, #[], fun i => Fin.elim0 i⟩] = true',
         'check [⟨0, #[0], fun i => Fin.elim0 i⟩] = true'),
        ('samples','check [⟨3, #[1, 3, 5], fun i => 2 * i.val + 1⟩] = true',
         'check [⟨3, #[1, 4, 5], fun i => 2 * i.val + 1⟩] = true'),
        ('extent','check [⟨2, #[0, 1], fun i => i.val⟩] = true',
         'check [⟨2, #[0, 1, 2], fun i => i.val⟩] = true'),
    ]
    for requests in ['SubwordSampleChecks.storeRequests','SubwordSampleChecks.byteRequests','ShiftSampleChecks.requests']:
        cases.append((requests,f'check {requests} = true',f'check ({requests} ++ [⟨0, #[0], fun i => Fin.elim0 i⟩]) = true'))
    for request,block in [('SubwordSampleChecks.byteLow','loadByteData.columns[1].blocks[1]?'),
                          ('ShiftSampleChecks.amount','byteShiftColumn2.blocks[0]?')]:
        original=f'(match ({block} : Option Airbender.Setup.Block) with | some (.periodic _ _ values) => values | _ => #[])'
        exact=f'{original} = {request}.values'
        changed=f'{original} = {request}.values.push 0'
        cases.append((request,exact,changed))
    for label,exact,changed in cases:
        for mutated,statement in [(False,exact),(True,changed)]:
            with tempfile.TemporaryDirectory(prefix='airbender-array-samples-') as directory:
                path=Path(directory)/'Check.lean'
                path.write_text(PREFIX+f'numeric_data_binding result : {statement}\nend ArraySampleControl\n')
                result=subprocess.run(['lean','-j1','-DElab.async=false',str(path)],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            if not mutated and result.returncode:raise SystemExit(f'Exact {label} failed:\n'+result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit(f'Changed {label} did not fail in the kernel:\n'+result.stdout[-2000:])
    print(f'PASS {len(cases)} exact array sample controls; kernel rejects all {len(cases)} mutations')


if __name__=='__main__':main()
