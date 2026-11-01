#!/usr/bin/env python3
"""Check original port classes, both erasure scopes and exact source fidelity."""
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
    for case in generator.CASES:
        owner='Airbender.Compiler.MemoryFrameChecks.'+case
        cases.append((case,f'check {owner}.data = true',f'check {{{owner}.data with placement := .branch 1 (.leaf []) (.leaf [])}} = true',case))
        cases.append((case+' binding',f'{owner}.data = '+generator.source(case),
            f'{{{owner}.data with activeMask := {owner}.data.activeMask+1}} = '+generator.source(case),case))
        native='Airbender.Compiler.MemoryFrameNative.'+case+'.native';memory='Airbender.Compiler.MemoryNative.'+case+'.native'
        encoded=f'{native}.ramFields.map (fun field => NumericPolynomialChecks.encode (field.polynomial {memory}.sourcePlacement))'
        cases.append((case+' complete fields',f'{owner}.data.ram = {encoded}',f'{owner}.data.ram.drop 1 = {encoded}',case))
    for label,exact,changed,case in cases:
        imports=('import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.'+case+'.Certificate\n') if case else ''
        for mutated,statement in [(False,exact),(True,changed)]:
            result=run(imports+PREFIX+f'numeric_data_binding result : {statement}\nend MemoryFrameControl\n')
            if not mutated and result.returncode:raise SystemExit(f'Exact {label} failed:\n'+result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit(f'Changed {label} did not fail in the kernel:\n'+result.stdout[-2000:])
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
