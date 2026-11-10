#!/usr/bin/env python3
"""Check original port classes, both erasure scopes and exact source fidelity."""
import argparse
from pathlib import Path
import subprocess
import tempfile
from unittest.mock import patch
import gkr_packed_memory_frame as generator
from gkr_memory_frame_instances import module

ROOT=Path(__file__).resolve().parents[1]
PREFIX='''import Airbender.Proofs.GKRProtocol.NumericMemoryFrameChecks
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
open Airbender Airbender.Compiler NumericMemoryFrameChecks
namespace MemoryFrameControl
set_option maxRecDepth 8192
def tiny : Capture := ⟨2, 2, .leaf [0], .leaf [0], .leaf [0], .leaf [0],
  [[(1,[0]),(0,[])]], [[(1,[0])]], [[(1,[0])]]⟩
def external : Capture := {tiny with nativeAddress := .leaf [AddressUniqueChecks.addressCode (.ScratchSpace 0)]}
'''


def run(source):
    with tempfile.TemporaryDirectory(prefix='airbender-memory-frame-') as directory:
        path=Path(directory)/'Check.lean';path.write_text(source)
        return subprocess.run(['lean','--tstack=32768','-j1','-DElab.async=false',str(path)],cwd=ROOT,
            stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case',choices=generator.CASES,action='append')
    args=parser.parse_args()
    exact='check tiny = true';cases=[]
    for label,changed in [('active erasure','{tiny with activeMask := 1}'),('all erasure','{tiny with allMask := 1}'),
            ('placement','{tiny with placement := .leaf [1]}'),('full bank exclusion','{tiny with inputAddress := .leaf [1]}'),
            ('branch size','{tiny with placement := .branch 1 (.leaf []) (.leaf [0])}')]:
        cases.append((label,exact,f'check ({changed}) = true',None))
    cases.append(('external full bank','check external = true',
        'check {external with fullAddress := external.nativeAddress} = true',None))
    for label,address in [('setup','.Setup 0'),('range16','.VirtualSetup .RangeCheck16Bits'),('timestamp','.VirtualSetup .RangeCheckTimestamp')]:
        cases.append((label,'check external = true',f'check {{external with nativeAddress := .leaf [AddressUniqueChecks.addressCode ({address})]}} = true',None))
    allowed='check {external with nativeAddress := .leaf [AddressUniqueChecks.addressCode (.VirtualSetup .InitsAndTeardownsLow)]} = true'
    rejected='check {external with nativeAddress := .leaf [AddressUniqueChecks.addressCode (.VirtualSetup .InitsAndTeardownsLow)], fullAddress := .leaf [AddressUniqueChecks.addressCode (.VirtualSetup .InitsAndTeardownsLow)]} = true'
    cases.append(('initialization oracle class',allowed,rejected,None))
    cases.append(('complete zero term','tiny.ram = [[(1,[0]),(0,[])]]','tiny.ram = [[(1,[0])]]',None))
    if args.case:cases=[]
    for case in args.case or generator.CASES:
        owner='Airbender.Compiler.MemoryFrameChecks.'+case
        cases.append((case,f'check {owner}.data = true',f'check {{{owner}.data with placement := .branch 1 (.leaf []) (.leaf [])}} = true',case))
        if case in generator.SMALL_CASES:
            cases.append((case+' binding',f'{owner}.data = '+generator.source(case),
                f'{{{owner}.data with activeMask := {owner}.data.activeMask+1}} = '+generator.source(case),case))
            native='Airbender.Compiler.MemoryFrameNative.'+case+'.native';memory='Airbender.Compiler.MemoryNative.'+case+'.native'
            encoded=f'{native}.ramFields.map (fun field => NumericPolynomialChecks.encode (field.polynomial {memory}.sourcePlacement))'
            cases.append((case+' complete fields',f'{owner}.data.ram = {encoded}',f'{owner}.data.ram.drop 1 = {encoded}',case))
        else:
            from gkr_packed_memory_frame_bounded import capture_shape
            _,arity,size=capture_shape(case)
            native='Airbender.Compiler.MemoryFrameNative.'+case+'.native'
            expected=f'NumericQueryFrameChecks.coordinateMask ({native}.activeCoordinates.map Fin.val)'
            cases.append((case+' mask',f'{owner}.data.activeMask = {expected}',f'{owner}.data.activeMask+1 = {expected}',case))
            if case.startswith('Unified'):
                expected=f'NumericQueryFrameChecks.coordinateMask ({native}.allCoordinates.map Fin.val)'
                cases.append((case+' initialization mask',f'{owner}.data.allMask = {expected}',f'{owner}.data.allMask+1 = {expected}',case))
                expected=f'{native}.initializationFields.map {owner}.encodeField'
                cases.append((case+' complete initialization',f'{owner}.data.initialization = {expected}',f'{owner}.data.initialization.drop 1 = {expected}',case))
            for field in (['placement','nativeAddress','inputAddress','fullAddress'] if case.startswith('BlakeRound') else []):
                for first in [0,(arity-1)//32*32]:
                    length=min(32,arity-first)
                    values=f'({owner}.data.{field}.toList.drop {first}).take {length}'
                    expected=f'NumericQueryFrameChecks.window {owner}.{field}Source {first} {length} (by decide +kernel)'
                    cases.append((case+f' {field} window {first}',f'{values} = {expected}',f'({values}).drop 1 = {expected}',case))
            for first in [0,(size-1)//16*16]:
                length=min(16,size-first)
                expected=f'(({native}.ramFields.drop {first}).take {length}).map {owner}.encodeField'
                values=f'({owner}.data.ram.drop {first}).take {length}'
                cases.append((case+f' RAM window {first}',f'{values} = {expected}',f'({values}).drop 1 = {expected}',case))
    for label,exact,changed,case in cases:
        imports=('import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.'+case+'.Certificate\n') if case else ''
        for mutated,statement in [(False,exact),(True,changed)]:
            result=run(imports+PREFIX+f'numeric_data_binding result : {statement}\nend MemoryFrameControl\n')
            if not mutated and result.returncode:raise SystemExit(f'Exact {label} failed:\n'+result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit(f'Changed {label} did not fail in the kernel:\n'+result.stdout[-2000:])
        print('PASS memory-frame control:',label,flush=True)
    if args.case:
        print(f'PASS {len(cases)} exact memory-frame capture controls; kernel rejects all {len(cases)} mutations')
        return
    with patch.object(generator,'CASES',()):legacy=module('add-sub-cached','AddSubCached')[1]
    result=run(legacy)
    if result.returncode:raise SystemExit('Legacy finalizer failed:\n'+result.stdout[-2000:])
    result=run('''import Airbender.Import.GKRProtocol.NumericMemoryFrameImport
open Airbender.Compiler
opaque hidden : NumericMemoryFrameChecks.Capture := ⟨0,0,.leaf [],.leaf [],.leaf [],.leaf [],[],[],[]⟩
numeric_memory_frame_capture rejected := hidden
''')
    if not result.returncode or 'did not reduce to closed numeric data' not in result.stdout:
        raise SystemExit('Opaque memory payload was not rejected:\n'+result.stdout[-2000:])
    print(f'PASS {len(cases)} exact memory-frame controls; kernel rejects all {len(cases)} mutations; legacy finalizer passes; opaque payload is rejected')


if __name__=='__main__':main()
