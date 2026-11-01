#!/usr/bin/env python3
"""Check all fixed Subword region lengths through exact numeric views."""
import argparse
import json
from export_gkr_translations import LEAN
from gkr_rom_columns import length
from gkr_unified_prefix import slice_block
from gkr_packed_rotate_boundary import preflight

COLUMNS=tuple(range(9))
REGIONS=['subwordZeroData','storePlaceData','storeClearData','loadHalfData','loadByteData']


def metadata_plan(column):
    artifact=json.loads((LEAN/'artifacts/setup/subword-memory.json').read_text())
    if [table['id'] for table in artifact['tables'][:5]]!=[0,29,30,42,43]:
        raise ValueError('fixed Subword region scope changed')
    entries=[]
    for index,table in enumerate(artifact['tables'][:5]):
        cursor=0;blocks=[]
        for block in artifact['columns'][column]['blocks']:
            start=max(cursor,table['offset']);stop=min(cursor+length(block),table['offset']+table['length'])
            if start<stop:blocks.extend(piece for _,piece in slice_block(block,start-cursor,stop-start))
            cursor+=length(block)
        if sum(map(length,blocks))!=table['length']:raise ValueError('fixed region length changed')
        entries.append(dict(index=index,table=table['id'],rows=table['length'],blocks=len(blocks),
                            source=f'(Airbender.Verification.{REGIONS[index]}.columns[({column} : Nat)])'))
    return entries


def modules(column):
    entries=metadata_plan(column)
    stem=f'Airbender.Proofs.GKRProtocol.SubwordRegionLengths.Column{column}'
    owner=f'Airbender.Compiler.SubwordRegionLengths.Column{column}'
    header=(f'namespace {owner}\nopen Airbender Airbender.Compiler\nopen PackedSetupEquality PackedSetupLengths\n'
            'set_option warningAsError true\nset_option Elab.async false\n\n')
    data='import Airbender.Import.PackedSetupEmbed\nimport Airbender.Proofs.GKRProtocol.PackedSetupLengths\n\n'+header
    data+='-- Import only the five fixed target regions.\nimport_setup_code_capture from "artifacts/setup/subword-memory.json" [\n'
    data+=',\n'.join(f'  region{e["index"]} := region {e["table"]} column {column} block_start 0 block_count {e["blocks"]} packed_bytes 0' for e in entries)+']\n\n'
    data+='noncomputable def requests : List Request := [\n  '+',\n  '.join(f'⟨region{e["index"]}, {e["rows"]}⟩' for e in entries)+']\n\n'
    yield stem+'.Data',data+'end '+owner+'\n'
    bindings=f'import {stem}.Data\nimport Airbender.Review.Helpers.Tables.Subword\nimport Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n'+header
    for e in entries:
        bindings+=f'numeric_data_binding binding{e["index"]} : {e["source"]}.blocks.toList = region{e["index"]}.map BlockCode.decode\n\n'
    yield stem+'.Bindings',bindings+'end '+owner+'\n'
    yield stem+'.Certificate',(f'import {stem}.Bindings\n\n'+header+
        'theorem checked : PackedSetupLengths.check requests = true := by decide +kernel\n\n'
        'theorem facts (index : Fin requests.length) : Fact (requests.get index) :=\n'
        '  PackedSetupLengths.check_sound_at requests checked index\n\nend '+owner+'\n')
    projected=f'import {stem}.Certificate\n\n'+header
    for e in entries:
        projected+=(f'theorem length{e["index"]} : ({e["source"]}.blocks.toList.map Setup.Block.length).sum = {e["rows"]} := by\n'
                    f'  rw [binding{e["index"]}]\n  exact facts ⟨{e["index"]}, by decide +kernel⟩\n\n')
    yield stem,projected+'end '+owner+'\n'


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--column',type=int,choices=COLUMNS,action='append')
    parser.add_argument('--write',action='store_true');parser.add_argument('--check',action='store_true');args=parser.parse_args()
    for column in args.column or COLUMNS:
        generated=list(modules(column))
        if args.write:preflight(generated)
        for module,source in generated:
            path=LEAN/(module.replace('.','/')+'.lean')
            if args.check and (not path.exists() or path.read_text()!=source):raise ValueError('fixed Subword lengths changed: '+module)
            if args.write and (not path.exists() or path.read_text()!=source):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
            print(module)


if __name__=='__main__':main()
