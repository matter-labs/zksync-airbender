#!/usr/bin/env python3
"""Check native ROM column spans with bounded block-length certificates."""
import argparse
import json
import os
import subprocess
from export_gkr_translations import LEAN

CHUNK=128
PER_MODULE=8


def length(block):
    if block['kind']=='affine':return block['length']
    return len(block['values'])*block.get('repetitions',1)


def modules(column):
    artifact=json.loads((LEAN/'artifacts/setup/unified.json').read_text())
    region=next(r for r in artifact['tables'] if r['id']==34)
    blocks=artifact['columns'][column]['blocks'];positions=[0]
    for block in blocks:positions.append(positions[-1]+length(block))
    first=next(i for i in range(len(blocks)) if positions[i+1]>region['offset'])
    stop=next(i for i in range(first+1,len(blocks)+1) if positions[i]>=region['offset']+region['length'])
    chunks=[(i,min(i+CHUNK,first)) for i in range(0,first,CHUNK)]
    ns=f'Airbender.Compiler.ROMColumns.Unified.Column{column}'
    full=f'Data.GKRSetup.Unified.setupColumn{column}'
    opts=('open Airbender Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\n'
      'set_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n')
    targets=[]
    for start in range(0,len(chunks),PER_MODULE):
        target=f'GKRProtocol.ROMParts.Unified.Column{column}.Part{start//PER_MODULE}'
        text=f'import GKRProtocol.BlockPartsImport\nimport Airbender.Data.GKRSetup.Unified\n\nnamespace {ns}\n'+opts
        for i in range(start,min(start+PER_MODULE,len(chunks))):
            lo,hi=chunks[i]
            text+=f'column_blocks_part front{i} from {full} start {lo} stop {hi}\n\n'
            text+=f'theorem frontLength{i} : (front{i}.map Setup.Block.length).sum = {positions[hi]-positions[lo]} := by decide +kernel\n\n'
        text+='end '+ns+'\n';targets.append((target,text))
    target=f'GKRProtocol.ROMColumns.Unified.Column{column}'
    text=''.join('import '+t+'\n' for t,_ in targets)+'import GKRProtocol.BlockCoverageImport\nimport GKRProtocol.ColumnSlices\nimport Airbender.Data.GKRSetup.Unified\n\nnamespace '+ns+'\n'+opts
    text+=f'column_blocks_part selected from {full} start {first} stop {stop}\n'
    text+=f'column_blocks_part back from {full} start {stop} stop {len(blocks)}\n\n'
    fronts=', '.join('front'+str(i) for i in range(len(chunks)))
    pieces=fronts+', selected, back' if fronts else 'selected, back'
    text+=f'column_parts_cover sourceCoverage from {full} parts [{pieces}]\n\n'
    text+=f'noncomputable def front : List Setup.Block := ([{fronts}] : List (List Setup.Block)).flatten\n\n'
    text+='noncomputable def selectedColumn : Setup.Column := ⟨selected.toArray⟩\n\n'
    text+='theorem prefixLength : (front.map Setup.Block.length).sum = '+str(positions[first])+' := by\n'
    if chunks:
        text+='  simp only [front, List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, '+', '.join('frontLength'+str(i) for i in range(len(chunks)))+']\n  decide +kernel\n\n'
    else:text+='  rfl\n\n'
    span=positions[stop]-positions[first]
    text+=f'theorem selectedLength : (selectedColumn.blocks.toList.map Setup.Block.length).sum = {span} := by decide +kernel\n\n'
    assoc='List.append_assoc, ' if len(chunks)>1 else 'List.nil_append, ' if not chunks else ''
    text+=f'theorem sourceShape : {full}.blocks.toList = front ++ (selectedColumn.blocks.toList ++ back) := by\n  rw [sourceCoverage]\n  simp only [front, selectedColumn, List.toList_toArray, List.flatten_cons, List.flatten_nil, {assoc}List.append_nil]\n\n'
    shift=region['offset']-positions[first]
    text+=f'theorem column_value (index : Fin 1048576) :\n    {full}.get? ({region["offset"]} + index.val) = selectedColumn.get? ({shift} + index.val) := by\n'
    text+=f'  have actual := column_slice_value {full} selectedColumn front back {positions[first]} {span}\n    sourceShape prefixLength selectedLength ({shift} + index.val) (by have := index.isLt; omega)\n'
    text+=f'  simpa only [show {positions[first]} + ({shift} + index.val) = {region["offset"]} + index.val by omega] using actual\n\nend {ns}\n'
    targets.append((target,text));return targets


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--column',type=int,choices=range(10),action='append')
    for flag in ['write','check','build']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args()
    for column in args.column or range(10):
        for target,text in modules(column):
            path=LEAN/(target.replace('.','/')+'.lean')
            if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('ROM span scaffold changed: '+target)
            if args.write and (not path.exists() or path.read_text()!=text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
            print(target,flush=True)
            if args.build:subprocess.run(['lake','--no-cache','build','+'+target+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)


if __name__=='__main__':main()
