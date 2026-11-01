#!/usr/bin/env python3
"""Check complete aligned samples from fixed native setup regions."""
import argparse
import json
from export_gkr_translations import LEAN
from gkr_rom_columns import length
from gkr_unified_prefix import slice_block
from gkr_packed_rotate_boundary import preflight

STEM='Airbender.Proofs.Tables.AlignedSampleChecks'
OWNER='Airbender.Verification.AlignedSampleChecks'
CAPTURES=[('conditional','jump-branch',31,1,128,'conditionalValue (index.val * 32768)',
           '(conditionalData.columns[1]).blocks.toList'),
          ('position','shift-binop',9,0,8,'index.val / 2','byteShiftColumn0.blocks.toList')]


def block_count(artifact,table,column):
    data=json.loads((LEAN/f'artifacts/setup/{artifact}.json').read_text())
    region=next(region for region in data['tables'] if region['id']==table)
    cursor=0;blocks=[]
    for block in data['columns'][column]['blocks']:
        start=max(cursor,region['offset']);stop=min(cursor+length(block),region['offset']+region['length'])
        if start<stop:blocks.extend(piece for _,piece in slice_block(block,start-cursor,stop-start))
        cursor+=length(block)
    if not blocks or any(block['kind']!='affine' or block['step']!=0 or length(block)%32768 for block in blocks):
        raise ValueError('fixed aligned sample geometry changed')
    return len(blocks)


def modules():
    header=f'namespace {OWNER}\nopen Airbender Airbender.Compiler PackedSetupEquality PackedSetupSamples\nset_option warningAsError true\nset_option Elab.async false\n\n'
    data=('import Airbender.Import.PackedSetupEmbed\nimport Airbender.Proofs.GKRProtocol.PackedSetupSamples\n'
          'import Airbender.Proofs.Tables.ReferenceControl\n\n'+header)
    for name,artifact,table,column,count,expected,_ in CAPTURES:
        size=block_count(artifact,table,column)
        data+=(f'import_setup_code_capture from "artifacts/setup/{artifact}.json" [\n'
               f'  {name}Blocks := region {table} column {column} block_start 0 block_count {size} packed_bytes 0\n]\n\n'
               f'def {name} : Request := ⟨{name}Blocks, {count}, fun index => {expected}⟩\n\n'
               f'def {name}Requests : List Request := [{name}]\n\n')
    yield STEM+'.Data',data+'end '+OWNER+'\n'
    bindings=(f'import {STEM}.Data\nimport Airbender.Data.Tables.Shift.Column0\n'
              'import Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n'+header)
    for name,_,_,_,_,_,original in CAPTURES:
        bindings+=f'numeric_data_binding {name}Binding : {original} = {name}Blocks.map BlockCode.decode\n\n'
    yield STEM+'.Bindings',bindings+'end '+OWNER+'\n'
    certificate=f'import {STEM}.Bindings\n\n'+header
    for name,*_ in CAPTURES:
        certificate+=(f'theorem {name}Checked : PackedSetupSamples.check {name}Requests = true := by decide +kernel\n\n'
                      f'theorem {name}Fact : Fact {name} :=\n'
                      f'  PackedSetupSamples.check_sound_at {name}Requests {name}Checked ⟨0, by decide +kernel⟩\n\n')
    yield STEM+'.Certificate',certificate+'end '+OWNER+'\n'


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--write',action='store_true');parser.add_argument('--check',action='store_true');args=parser.parse_args()
    generated=list(modules())
    if args.write:preflight(generated)
    for module,source in generated:
        path=LEAN/(module.replace('.','/')+'.lean')
        if args.check and (not path.exists() or path.read_text()!=source):raise ValueError('fixed aligned samples changed: '+module)
        if args.write and (not path.exists() or path.read_text()!=source):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
        print(module)


if __name__=='__main__':main()
