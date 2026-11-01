#!/usr/bin/env python3
"""Require exact numeric frame checks, source binding and the legacy finalizer."""
from pathlib import Path
import subprocess
import tempfile
import argparse
from unittest.mock import patch
import gkr_packed_query_frame
from gkr_query_frame_instances import module

ROOT=Path(__file__).resolve().parents[1]
PREFIX='''import Airbender.Proofs.GKRProtocol.NumericQueryFrameIndexedChecks
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
open Airbender Airbender.Compiler NumericQueryFrameChecks
namespace QueryFrameControl
set_option maxRecDepth 8192
def tiny : Capture := ⟨[1], [0], [7], [7], [([(1, [0]), (0, [])], [(1, [0]), (0, [])])]⟩
'''


def run(source):
    with tempfile.TemporaryDirectory(prefix='airbender-query-frame-') as directory:
        path=Path(directory)/'Check.lean';path.write_text(source)
        return subprocess.run(['lean','--tstack=32768','-j1','-DElab.async=false',str(path)],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case',choices=gkr_packed_query_frame.CASES,action='append')
    args=parser.parse_args()
    selected=args.case or gkr_packed_query_frame.CASES
    exact='NumericQueryFrameChecks.check tiny = true'
    changes=[('erasure','{tiny with coordinates := [0]}'),('placement','{tiny with placement := [1]}'),
             ('round trip','{tiny with returnedAddress := [8]}'),
             ('coefficient','{tiny with fields := [([(1, [0]), (0, [])], [(2, [0]), (0, [])])]}'),
             ('complete terms','{tiny with fields := [([(1, [0]), (0, [])], [(1, [0])])]}')]
    cases=[(label,exact,f'NumericQueryFrameChecks.check ({changed}) = true') for label,changed in changes]
    for case in selected:
        owner='Airbender.Compiler.QueryFrameChecks.'+case
        if case in gkr_packed_query_frame.LARGE_CASES:
            cases.append((case,f'indexedCheck {owner}.views {owner}.data.fields = true',
                f'indexedCheck {owner}.views ({owner}.data.fields ++ [([], [(1, [])])]) = true'))
            native='Airbender.Compiler.QueryFrameNative.'+case+'.native'
            cases.append((case+' binding',f'{owner}.data.coordinates = {native}.coordinates.map Fin.val',
                f'{owner}.data.coordinates ++ [999] = {native}.coordinates.map Fin.val'))
            arity,size=gkr_packed_query_frame.capture_shape(case)
            field_first=((size-1)//16)*16;field_count=size-field_first
            encoded=f'(({native}.fields.drop {field_first}).take {field_count}).map {owner}.encodeField'
            cases.append((case+' final field binding',
                f'({owner}.data.fields.drop {field_first}).take {field_count} = {encoded}',
                f'({owner}.data.fields.drop {field_first}).take {field_count-1} = {encoded}'))
            map_first=((arity-1)//32)*32;map_count=arity-map_first
            mapped=f'window {owner}.placementSource {map_first} {map_count} (by decide)'
            cases.append((case+' final placement binding',
                f'({owner}.data.placement.drop {map_first}).take {map_count} = {mapped}',
                f'({owner}.data.placement.drop {map_first}).take {map_count-1} = {mapped}'))
            continue
        cases.append((case,f'NumericQueryFrameChecks.check {owner}.data = true',
                      f'NumericQueryFrameChecks.check ({{{owner}.data with fields := {owner}.data.fields ++ [([], [(1, [])])]}}) = true'))
        expected=gkr_packed_query_frame.source(case)
        cases.append((case+' binding',f'{owner}.data = {expected}',
                      f'{{{owner}.data with coordinates := {owner}.data.coordinates ++ [999]}} = {expected}'))
    indexed='indexedCheck (index tiny) tiny.fields = true'
    for label,changed in [
        ('indexed erasure','{index tiny with coordinates := 1}'),
        ('indexed placement','{index tiny with placement := .leaf [1]}'),
        ('indexed round trip','{index tiny with returnedAddress := .leaf [8]}'),
        ('indexed branch size','{index tiny with placement := .branch 1 (.leaf []) (.leaf [0])}')]:
        cases.append((label,indexed,f'indexedCheck ({changed}) tiny.fields = true'))
    cases.append(('indexed complete terms',indexed,
        'indexedCheck (index tiny) [([(1, [0]), (0, [])], [(1, [0])])] = true'))
    cases.append(('bounded source window',
        '[2,3,4] = window (fun wire : Fin 8 => wire.val) 2 3 (by decide)',
        '[2,3] = window (fun wire : Fin 8 => wire.val) 2 3 (by decide)'))
    cases.append(('mask source binding','(index tiny).coordinates = coordinateMask tiny.coordinates',
        '(index tiny).coordinates + 1 = coordinateMask tiny.coordinates'))
    for label,exact,changed in cases:
        for mutated,statement in [(False,exact),(True,changed)]:
            capture=next((case for case in selected if label.startswith(case)),None)
            imports=('import Airbender.Proofs.GKRProtocol.QueryFrameChecks.'+capture+'.Certificate\n') if capture else ''
            result=run(imports+PREFIX+f'numeric_data_binding result : {statement}\nend QueryFrameControl\n')
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
    result=run('''import Airbender.Import.GKRProtocol.NumericQueryFrameIndexImport
open Airbender.Compiler
opaque hidden : NumericQueryFrameChecks.Index := ⟨0, .leaf [], .leaf [], .leaf []⟩
numeric_query_frame_index rejected := hidden
''')
    if not result.returncode or 'did not reduce to closed numeric data' not in result.stdout:
        raise SystemExit('Opaque index was not rejected:\n'+result.stdout[-2000:])
    print(f'PASS {len(cases)} exact query-frame controls; kernel rejects all {len(cases)} mutations; legacy finalizer passes; opaque data is rejected')


if __name__=='__main__':main()
