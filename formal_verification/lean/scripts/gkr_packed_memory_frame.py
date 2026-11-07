#!/usr/bin/env python3
"""Check complete native memory frames after exact numeric source binding."""
import argparse
from export_gkr_translations import LEAN
from gkr_packed_rotate_boundary import preflight

from gkr_wiring_instances import CASES as CIRCUIT_CASES

# These four frame captures belonged only to the retired captured execution wrappers.
RETIRED_STEMS=('JumpBranch','MulDiv','ShiftBinop','Unified')
SMALL_CASES=('AddSubCached',)
LARGE_CASES=tuple(stem+mode for stem in CIRCUIT_CASES if stem!='AddSub' and stem not in RETIRED_STEMS for mode in ['Cached'])
CASES=SMALL_CASES+LARGE_CASES


def source(case):
    root='Airbender.Compiler.'
    original=root+'MemoryFrameNative.'+case+'.native'
    memory=root+'MemoryNative.'+case+'.native'
    base=root+'FullArithmeticNative.'+case+'.native'
    return (f'NumericMemoryFrameChecks.ofTyped {original}.ramFields {original}.initializationFields {original}.executeFields\n'
        f'  {memory}.sourcePlacement {memory}.bank {original}.activeCoordinates {original}.allCoordinates\n'
        f'  {base}.inputBank {base}.bank')


def small_modules(case):
    stem='Airbender.Proofs.GKRProtocol.MemoryFrameChecks.'+case
    owner='Airbender.Compiler.MemoryFrameChecks.'+case
    header=f'namespace {owner}\nopen Airbender Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 8192\n\n'
    end='\nend '+owner+'\n'
    yield stem+'.Data',(f'import Airbender.Proofs.GKRProtocol.MemoryFrameNative.{case}Inputs\n'
        'import Airbender.Import.GKRProtocol.NumericMemoryFrameImport\n\n'+header+
        'set_option exponentiation.threshold 4096 in\nnumeric_memory_frame_capture data := '+source(case)+end)
    yield stem+'.Bindings',(f'import {stem}.Data\nimport Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n'+header+
        'numeric_data_binding source_binding : data = '+source(case)+end)
    original='Airbender.Compiler.MemoryFrameNative.'+case+'.native'
    memory='Airbender.Compiler.MemoryNative.'+case+'.native'
    base='Airbender.Compiler.FullArithmeticNative.'+case+'.native'
    predicates=[]
    for name,coordinates in [('ram','activeCoordinates'),('initialization','allCoordinates'),('execute','allCoordinates')]:
        predicates.append(f'{original}.{name}Fields.all (fun field =>\n'
            f'    field.baseFrameCheck {memory}.sourcePlacement {memory}.bank {original}.{coordinates} {base}.inputBank {base}.bank) = true')
    yield stem+'.Certificate',(f'import {stem}.Bindings\n\n'+header+
        'theorem checked : NumericMemoryFrameChecks.check data = true := by decide +kernel\n\n'
        'theorem originalChecked : '+' ∧\n  '.join(predicates)+' :=\n'
        f'  NumericMemoryFrameChecks.check_sound_of_binding data {original}.ramFields {original}.initializationFields {original}.executeFields\n'
        f'    {memory}.sourcePlacement {memory}.bank {original}.activeCoordinates {original}.allCoordinates\n'
        f'    {base}.inputBank {base}.bank source_binding checked\n'+end)


def modules(case):
    if case in LARGE_CASES:
        from gkr_packed_memory_frame_bounded import modules as bounded_modules
        certificate=dict(small_modules(case))['Airbender.Proofs.GKRProtocol.MemoryFrameChecks.'+case+'.Certificate']
        yield from bounded_modules(case,source(case),certificate)
    else:yield from small_modules(case)


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--case',choices=CASES,action='append')
    parser.add_argument('--write',action='store_true');parser.add_argument('--check',action='store_true');args=parser.parse_args()
    for case in args.case or CASES:
        generated=list(modules(case))
        if args.write:preflight(generated)
        for module,text in generated:
            path=LEAN/(module.replace('.','/')+'.lean')
            if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('numeric memory frame changed: '+module)
            if args.write and (not path.exists() or path.read_text()!=text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
            print(module)


if __name__=='__main__':main()
