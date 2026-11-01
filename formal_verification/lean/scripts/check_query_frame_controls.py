#!/usr/bin/env python3
"""Require exact numeric frame checks, source binding and the legacy finalizer."""
from pathlib import Path
import subprocess
import tempfile
from unittest.mock import patch
import gkr_packed_query_frame
from gkr_query_frame_instances import module

ROOT=Path(__file__).resolve().parents[1]
PREFIX='''import Airbender.Proofs.GKRProtocol.QueryFrameChecks.AddSubCached.Certificate
import Airbender.Proofs.GKRProtocol.QueryFrameChecks.AddSubUncached.Certificate
open Airbender Airbender.Compiler NumericQueryFrameChecks
namespace QueryFrameControl
def tiny : Capture := ⟨[1], [0], [7], [7], [([(1, [0]), (0, [])], [(1, [0]), (0, [])])]⟩
'''


def run(source):
    with tempfile.TemporaryDirectory(prefix='airbender-query-frame-') as directory:
        path=Path(directory)/'Check.lean';path.write_text(source)
        return subprocess.run(['lean','-j1','-DElab.async=false',str(path)],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)


def main():
    exact='NumericQueryFrameChecks.check tiny = true'
    changes=[('erasure','{tiny with coordinates := [0]}'),('placement','{tiny with placement := [1]}'),
             ('round trip','{tiny with returnedAddress := [8]}'),
             ('coefficient','{tiny with fields := [([(1, [0]), (0, [])], [(2, [0]), (0, [])])]}'),
             ('complete terms','{tiny with fields := [([(1, [0]), (0, [])], [(1, [0])])]}')]
    cases=[(label,exact,f'NumericQueryFrameChecks.check ({changed}) = true') for label,changed in changes]
    for case in gkr_packed_query_frame.CASES:
        owner='Airbender.Compiler.QueryFrameChecks.'+case
        cases.append((case,f'NumericQueryFrameChecks.check {owner}.data = true',
                      f'NumericQueryFrameChecks.check ({{{owner}.data with fields := {owner}.data.fields ++ [([], [(1, [])])]}}) = true'))
        expected=gkr_packed_query_frame.source(case)
        cases.append((case+' binding',f'{owner}.data = {expected}',
                      f'{{{owner}.data with coordinates := {owner}.data.coordinates ++ [999]}} = {expected}'))
    for label,exact,changed in cases:
        for mutated,statement in [(False,exact),(True,changed)]:
            result=run(PREFIX+f'numeric_data_binding result : {statement}\nend QueryFrameControl\n')
            if not mutated and result.returncode:raise SystemExit(f'Exact {label} failed:\n'+result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit(f'Changed {label} did not fail in the kernel:\n'+result.stdout[-2000:])
    with patch.object(gkr_packed_query_frame,'CASES',()):
        legacy=module('add-sub-cached','AddSubCached')[1]
    result=run(legacy)
    if result.returncode:raise SystemExit('Legacy finalizer control failed:\n'+result.stdout[-2000:])
    result=run('''import Airbender.Import.GKRProtocol.NumericQueryFrameImport
open Airbender.Compiler
opaque hidden : NumericQueryFrameChecks.Capture := ⟨[], [], [], [], []⟩
numeric_query_frame_capture rejected := hidden
''')
    if not result.returncode or 'did not reduce to closed numeric data' not in result.stdout:
        raise SystemExit('Opaque source was not rejected:\n'+result.stdout[-2000:])
    print(f'PASS {len(cases)} exact query-frame controls; kernel rejects all {len(cases)} mutations; legacy finalizer passes; opaque data is rejected')


if __name__=='__main__':main()
