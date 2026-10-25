#!/usr/bin/env python3
"""Check the actual subword prefix against retained slices in bounded block spans."""
import argparse
import json
import os
import subprocess
from export_gkr_translations import LEAN
from gkr_shift_prefix_instances import plans

REGIONS=['subwordZeroData','storePlaceData','storeClearData','loadHalfData','loadByteData','subwordROMHalfData','subwordROMByteData']
PREFIX=13238273
PER_MODULE=8


def modules(column):
    artifact=json.loads((LEAN/'artifacts/setup/subword-memory.json').read_text())
    stop,chunks=plans(artifact,column,prefix=PREFIX,chunk_size=1)
    ns=f'Airbender.Compiler.SubwordPrefixNative.Column{column}'
    full=f'Data.GKRSetup.SubwordMemory.setupColumn{column}'
    cols=[f'(Verification.{name}.columns[({column} : Nat)])' for name in REGIONS]
    opts=('open Airbender Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\n'
          'set_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n')
    targets=[]
    for begin in range(0,len(chunks),PER_MODULE):
        name=f'GKRProtocol.SubwordPrefixParts.Column{column}.Part{begin//PER_MODULE}'
        text=('import GKRProtocol.BlockPartsImport\nimport Airbender.Data.GKRSetup.SubwordMemory\n'
              'import Airbender.Review.Helpers.Tables.Subword\n\nnamespace '+ns+'\n'+opts)
        for i in range(begin,min(begin+PER_MODULE,len(chunks))):
            first,last,lo,hi,pieces=chunks[i]
            text+=f'column_blocks_part original{i} from {full} start {first} stop {last}\n'
            names=[]
            for kind,a,b in pieces:
                part=f'target{i}Region{kind}';names.append(part)
                text+=f'column_blocks_part {part} from {cols[kind]} start {a} stop {b}\n'
            text+=f'noncomputable def target{i} : List Setup.Block := '+' ++ '.join(names)+'\n\n'
            proof=f'exact congrArg normalizeSetupBlocks (show original{i} = target{i} from rfl)' if sum(b-a for _,a,b in pieces)==last-first else 'rfl'
            text+=f'theorem chunkChecked{i} : normalizeSetupBlocks original{i} = normalizeSetupBlocks target{i} := by\n  {proof}\n\n'
            text+=f'theorem chunkLength{i} : (original{i}.map Setup.Block.length).sum = {hi-lo} := by decide +kernel\n\n'
        text+='end '+ns+'\n';targets.append((name,text))
    name=f'GKRProtocol.SubwordPrefixNative.Column{column}'
    text=''.join('import '+n+'\n' for n,_ in targets)+'import GKRProtocol.BlockCoverageImport\n\nnamespace '+ns+'\n'+opts
    text+=f'column_blocks_part suffix from {full} start {stop} stop {len(artifact["columns"][column]["blocks"])}\n'
    for stem in ['original','target']:
        text+=f'noncomputable def {stem}s : List (List Setup.Block) := ['+', '.join(stem+str(i) for i in range(len(chunks)))+']\n\n'
    text+='noncomputable def target : List Setup.Block := '+' ++ '.join(c+'.blocks.toList' for c in cols)+'\n\n'
    text+=f'column_parts_cover sourceCoverage from {full} parts ['+', '.join('original'+str(i) for i in range(len(chunks)))+', suffix]\n\n'
    text+=f'theorem sourceShape : {full}.blocks.toList = originals.flatten ++ suffix := by\n  apply sourceCoverage.trans\n  simp only [originals, List.flatten_cons, List.flatten_nil, '+('List.append_assoc, ' if len(chunks)>1 else '')+'List.append_nil]\n\n'
    for kind,col in enumerate(cols):
        pieces=[f'target{i}Region{kind}' for i,chunk in enumerate(chunks) if any(k==kind for k,_,_ in chunk[-1])]
        text+=f'column_parts_cover regionShape{kind} from {col} parts ['+', '.join(pieces)+']\n\n'
    text+='theorem targetShape : target = targets.flatten := by\n  rw [target, '+', '.join(f'regionShape{i}' for i in range(7))+']\n'
    text+='  simp only [targets, '+', '.join('target'+str(i) for i in range(len(chunks)))+', List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]\n\n'
    checks='List.Forall₂.nil'
    for i in reversed(range(len(chunks))):checks=f'List.Forall₂.cons chunkChecked{i} ({checks})'
    text+='theorem chunksChecked : List.Forall₂ (fun left right => normalizeSetupBlocks left = normalizeSetupBlocks right) originals targets :=\n  '+checks+'\n\n'
    text+=f'theorem prefixLength : (originals.flatten.map Setup.Block.length).sum = {PREFIX} := by\n'
    text+='  simp only [originals, List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, '+', '.join('chunkLength'+str(i) for i in range(len(chunks)))+']\n  rfl\n\n'
    text+=f'theorem prefix_value (index : Fin {PREFIX}) : {full}.get? index.val = Setup.getFromBlocks target index.val := by\n'
    text+='  change Setup.getFromBlocks '+full+'.blocks.toList index.val = _\n  rw [sourceShape, getFromBlocks_before_suffix _ _ index.val (by rw [prefixLength]; exact index.isLt), targetShape]\n  exact normalized_chunks_agree originals targets chunksChecked index.val\n\n'
    for i,col in enumerate(cols):
        size=artifact['tables'][i]['length'];offset=artifact['tables'][i]['offset']
        text+=f'theorem regionLength{i} : ({col}.blocks.toList.map Setup.Block.length).sum = {size} := by decide +kernel\n\n'
        front=' ++ '.join(c+'.blocks.toList' for c in cols[:i]) or '[]';back=' ++ '.join(c+'.blocks.toList' for c in cols[i+1:]) or '[]'
        text+=f'noncomputable def front{i} : List Setup.Block := {front}\nnoncomputable def back{i} : List Setup.Block := {back}\n\n'
        text+=f'theorem regionPrefix{i} : (front{i}.map Setup.Block.length).sum = {offset} := by\n'
        if i==0:text+='  rfl\n\n'
        elif i==1:text+='  exact regionLength0\n\n'
        else:text+=f'  simp only [front{i}, List.map_append, List.sum_append, '+', '.join(f'regionLength{j}' for j in range(i))+']\n\n'
        text+=f'theorem region_value{i} (index : Fin {size}) :\n    {full}.get? ({offset} + index.val) = {col}.get? index.val := by\n  rw [prefix_value ⟨{offset} + index.val, by have := index.isLt; omega⟩]\n'
        text+=f'  have shape : target = front{i} ++ ({col}.blocks.toList ++ back{i}) := by\n'
        rules='List.append_assoc'+(', List.append_nil' if i==6 else '')+(', List.nil_append' if i==0 else '')
        text+=f'    simp only [target, front{i}, back{i}, {rules}]\n  change Setup.getFromBlocks target ({offset} + index.val) = _\n  rw [shape]\n'
        text+=f'  have skipped := Setup.Proofs.skip_blocks front{i} ({col}.blocks.toList ++ back{i}) index.val\n  rw [regionPrefix{i}] at skipped\n'
        text+=f'  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength{i}]; exact index.isLt))\n\n'
    text+='end '+ns+'\n';targets.append((name,text));return targets


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--column',type=int,choices=range(9),action='append')
    for flag in ['write','check','build']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args()
    for col in args.column or range(9):
        for name,text in modules(col):
            path=LEAN/(name.replace('.','/')+'.lean')
            if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('subword prefix scaffold changed: '+name)
            if args.write and (not path.exists() or path.read_text()!=text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
            print(name,flush=True)
            if args.build:subprocess.run(['lake','--no-cache','build','+'+name+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)


if __name__=='__main__':main()
