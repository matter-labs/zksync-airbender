#!/usr/bin/env python3
"""Bind the complete native seven-bit XOR table to a packed checker."""
import argparse
import json
from pathlib import Path
from generate_packed_xor9 import block_length, term, ranges, tree, binding_tree
from gkr_unified_prefix import slice_block
from gkr_packed_rotate_boundary import preflight

ROOT=Path(__file__).resolve().parents[1]
BASE='Airbender.Proofs.Blake2G.Xor7'
OWNER='Airbender.Blake2G.Proofs.Xor7PackedCapture'


def native_blocks(artifact):
    region=next(table for table in artifact['tables'] if table['id']==19)
    if (region['length'],region['width'],region['key_columns'])!=(16384,3,2):
        raise ValueError('XOR7 native region dimensions changed')
    position=0;blocks=[]
    for block in artifact['columns'][2]['blocks']:
        size=block_length(block);lo=max(position,region['offset']);hi=min(position+size,region['offset']+region['length'])
        if lo<hi:blocks.extend(part for _,part in slice_block(block,lo-position,hi-lo))
        position+=size
    if sum(map(block_length,blocks))!=16384:raise ValueError('incomplete XOR7 native region')
    return blocks


def modules():
    blocks=native_blocks(json.loads((ROOT/'artifacts/setup/blake-g.json').read_text()))
    parts=ranges(0,len(blocks),4)
    data=('import Airbender.Proofs.Tables.PackedXor7Checks\nimport Airbender.Data.Setup.Blake2G.XorData\n'
          'import Airbender.Proofs.Tables.LiteralColumnParts\nimport Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n'
          f'namespace {OWNER}\nopen Airbender.Setup Airbender.Setup.Proofs PackedWordBlocks\n'
          'set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 32768\n\n'
          'literal_column_parts column from (xor7Data.columns[2]) depth 4\n\n')
    for index,(first,stop) in enumerate(parts):data+=f'def blocks{index} : List Code := ['+', '.join(map(term,blocks[first:stop]))+']\n'
    data+='\ndef blocks : List Code := '+tree([f'blocks{i}' for i in range(16)])+'\n\n'
    for index in range(16):data+=f'numeric_data_binding binding{index} : blocks{index}.map (Code.decode 65536) = columnBlocks{index}.toList\n'
    data+='\ntheorem source_binding : blocks.map (Code.decode 65536) = (xor7Data.columns[2]).blocks.toList := by\n'
    data+='  change blocks.map (Code.decode 65536) = column.blocks.toList\n  have joined : column.blocks = '+tree([f'columnBlocks{i}' for i in range(16)])+' := rfl\n'
    data+='  rw [joined]\n  simpa only [blocks, List.map_append, Array.toList_append] using '+binding_tree(0,16)+'\n\nend '+OWNER+'\n'
    yield BASE+'PackedCapture',data
    yield BASE+'PackedCertificate',(f'import {BASE}PackedCapture\n\nnamespace {OWNER}\nopen Airbender.Setup.Proofs\n'
        'set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 32768\n\n'
        'theorem checked : PackedXor7Checks.check 0 blocks = true := by decide +kernel\n\nend '+OWNER+'\n')
    yield BASE+'Certificate',(f'import {BASE}PackedCertificate\n\nnamespace Airbender.Blake2G.Proofs.XorCertificate\n'
        'open Airbender.Setup Airbender.Setup.Proofs\nset_option warningAsError true\nset_option Elab.async false\n\n'
        'theorem output7 : checkBlocks (fun n => n / 128 ^^^ n % 128) 0\n'
        "    (xor7Data.columns[2]'(by omega)).blocks.toList = true := by\n"
        '  rw [← Xor7PackedCapture.source_binding]\n'
        '  exact PackedXor7Checks.check_sound 0 Xor7PackedCapture.blocks Xor7PackedCapture.checked\n\n'
        'end Airbender.Blake2G.Proofs.XorCertificate\n')


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--write',action='store_true');parser.add_argument('--check',action='store_true');args=parser.parse_args()
    generated=list(modules())
    if args.write:preflight(generated)
    for name,source in generated:
        path=ROOT/(name.replace('.','/')+'.lean')
        if args.check and (not path.exists() or path.read_text()!=source):raise ValueError('complete XOR7 capture changed: '+name)
        if args.write and (not path.exists() or path.read_text()!=source):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
        print(name)


if __name__=='__main__':main()
