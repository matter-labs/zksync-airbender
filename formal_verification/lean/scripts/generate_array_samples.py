#!/usr/bin/env python3
"""Bind complete fixed table samples to their numeric kernel checks."""
import argparse
import json
from export_gkr_translations import LEAN
from gkr_rom_columns import length
from gkr_unified_prefix import slice_block
from gkr_packed_rotate_boundary import preflight

SAMPLES=[
    ('subword-memory',29,1,1,'storeHigh','storePlaceData','256 * index.val'),
    ('subword-memory',43,1,1,'byteLow','loadByteData','if index.val < 128 then index.val else index.val + 65280'),
    ('subword-memory',43,2,1,'byteHigh','loadByteData','if index.val < 128 then 65535 else 0'),
    ('shift-binop',9,2,0,'amount','byteShiftColumn2','index.val / 8'),
]


def values(spec):
    artifact,table,column,index,*_=spec
    data=json.loads((LEAN/f'artifacts/setup/{artifact}.json').read_text())
    region=next(region for region in data['tables'] if region['id']==table)
    if table in [34,44,45]:raise ValueError('program table is outside the sample scope')
    cursor=0;blocks=[]
    for block in data['columns'][column]['blocks']:
        start=max(cursor,region['offset']);stop=min(cursor+length(block),region['offset']+region['length'])
        if start<stop:blocks.extend(piece for _,piece in slice_block(block,start-cursor,stop-start))
        cursor+=length(block)
    block=blocks[index]
    if block['kind']!='periodic' or len(block['values'])!=256:
        raise ValueError('fixed sample geometry changed')
    return block['values']


def modules():
    for family,specs in [('Subword',SAMPLES[:3]),('Shift',SAMPLES[3:])]:
        owner=f'Airbender.Verification.{family}SampleChecks'
        stem=f'Airbender.Proofs.Tables.{family}SampleChecks'
        header=f'namespace {owner}\nopen ArraySampleChecks\nset_option warningAsError true\nset_option Elab.async false\n\n'
        source='import Airbender.Proofs.Tables.ArraySampleChecks\n\n'+header
        for spec in specs:
            name=spec[4]
            source+=f'def {name} : Request := ⟨256, #['+', '.join(map(str,values(spec)))+f'], fun index => {spec[6]}⟩\n\n'
        captures=[('storeRequests','storeChecked',[('storeHigh','storeFact')]),('byteRequests','byteChecked',[('byteLow','byteLowFact'),('byteHigh','byteHighFact')])] if family=='Subword' else [('requests','checked',[('amount','fact')])]
        for requests,checked,entries in captures:
            source+=f'def {requests} : List Request := ['+', '.join(name for name,_ in entries)+']\n\n'
            source+=f'theorem {checked} : check {requests} = true := by decide +kernel\n\n'
            for index,(name,fact) in enumerate(entries):
                source+=f'theorem {fact} : Fact {name} :=\n  check_sound_at {requests} {checked} ⟨{index}, by decide +kernel⟩\n\n'
        yield stem,source+'end '+owner+'\n'
        binding_owner=f'Airbender.Verification.{family}SampleBindings'
        imports=('import Airbender.Data.Tables.Subword.StorePlaceData\nimport Airbender.Data.Tables.Subword.LoadByteData\n' if family=='Subword' else 'import Airbender.Data.Tables.Shift.Column2\n')
        source=imports+f'import {stem}\nimport Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\nnamespace {binding_owner}\nopen Setup\nset_option warningAsError true\nset_option Elab.async false\n\n'
        for _,_,column,index,name,data,_ in specs:
            block=f'{data}.blocks[{index}]?' if family=='Shift' else f'{data}.columns[{column}].blocks[{index}]?'
            source+=(f'numeric_data_binding {name}Binding : (match ({block} : Option Block) with\n'
                     f'  | some (.periodic _ _ values) => values\n  | _ => #[]) = {owner}.{name}.values\n\n')
        yield f'Airbender.Proofs.Tables.{family}SampleBindings',source+'end '+binding_owner+'\n'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true');parser.add_argument('--check',action='store_true');args=parser.parse_args()
    generated=list(modules())
    if args.write:preflight(generated)
    for module,source in generated:
        path=LEAN/(module.replace('.','/')+'.lean')
        if args.check and (not path.exists() or path.read_text()!=source):raise ValueError('fixed array samples changed: '+module)
        if args.write and (not path.exists() or path.read_text()!=source):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
        print(module)


if __name__=='__main__':main()
