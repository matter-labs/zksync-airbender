#!/usr/bin/env python3
"""Assemble bounded unified prefix certificates and independently imported regions."""
import argparse
import os
import subprocess
from export_gkr_translations import LEAN
from gkr_unified_prefix import plans,DATA,CHUNK,PREFIX
from gkr_unified_equal_chunks import PER_MODULE


def special_chunks(column):
    artifact,blocks,positions,stop,groups,regions=plans(column)
    for first in range(0,stop,CHUNK):
        last=min(first+CHUNK,stop)
        if all(e['mode']=='identical' for group in groups[first:last] for e in group):continue
        k=first//CHUNK;owner=f'Airbender.Compiler.UnifiedSpecialChunks.Column{column}.Chunk{k}'
        stem=f'GKRProtocol.UnifiedSpecialParts.Column{column}.Chunk{k}'
        name=f'GKRProtocol.UnifiedSpecialNative.Column{column}.Chunk{k}'
        text=''.join(f'import {stem}.Part{i}\n' for i in range((last-first+7)//8))+'import GKRProtocol.ChunkLengths\n\nnamespace '+owner+'\n'
        text+='open Airbender Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 16000000\n\n'
        text+='noncomputable def sources : List Setup.Block := ['+', '.join(f'source{i}' for i in range(first,last))+']\n\n'
        text+='noncomputable def targets : List (List Setup.Block) := ['+', '.join(f'target{i}' for i in range(first,last))+']\n\n'
        text+='noncomputable def target : List Setup.Block := targets.flatten\n\n'
        text+='theorem sourcesAgree : original = sources := by rfl\n\n'
        proof='List.Forall₂.nil'
        for i in reversed(range(first,last)):proof=f'List.Forall₂.cons (⟨length{i}, follows{i}⟩) ({proof})'
        text+='theorem spansChecked : List.Forall₂ (fun source target => (target.map Setup.Block.length).sum = source.length ∧ blockTargetsFollow source 0 target) sources targets :=\n  '+proof+'\n\n'
        text+='theorem chunkAgreement : blockChunkAgreement original target := by\n  rw [sourcesAgree]\n  exact block_partitions_chunk_agreement sources targets spansChecked\n\nend '+owner+'\n'
        yield name,text


def column_module(column):
    artifact,blocks,positions,stop,groups,regions=plans(column)
    equal=[];special=[]
    for first in range(0,stop,CHUNK):
        last=min(first+CHUNK,stop);k=first//CHUNK
        (equal if all(e['mode']=='identical' for group in groups[first:last] for e in group) else special).append(k)
    name=f'GKRProtocol.UnifiedAllPrefix.Column{column}';owner=f'Airbender.Compiler.UnifiedAllPrefix.Column{column}'
    text=''.join(f'import GKRProtocol.UnifiedEqualParts.Column{column}.Part{i}\n' for i in range((len(equal)+PER_MODULE-1)//PER_MODULE))
    text+=''.join(f'import GKRProtocol.UnifiedSpecialNative.Column{column}.Chunk{k}\n' for k in special)
    text+=''.join(f'import GKRProtocol.UnifiedSpecialLengths.Column{column}.Chunk{k}\n' for k in special)
    text+='import GKRProtocol.BlockCoverageImport\nimport GKRProtocol.ChunkSpans\n\nnamespace '+owner+'\n'
    text+='open Airbender Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 131072\nset_option maxHeartbeats 16000000\n\n'
    full=f'Data.GKRSetup.Unified.setupColumn{column}'
    def ns(k):return f'Airbender.Compiler.UnifiedEqualChunks.Column{column}' if k in equal else f'Airbender.Compiler.UnifiedSpecialChunks.Column{column}.Chunk{k}'
    def original(k):return ns(k)+('.original'+str(k) if k in equal else '.original')
    def target(k):return ns(k)+('.target'+str(k) if k in equal else '.target')
    count=(stop+CHUNK-1)//CHUNK
    for k in equal:
        text+=f'theorem chunkAgreement{k} : blockChunkAgreement {original(k)} {target(k)} := by\n  have same := {ns(k)}.chunkSame{k}\n  constructor\n  · exact congrArg (fun blocks : List Setup.Block => (blocks.map Setup.Block.length).sum) same\n  · intro index\n    rw [same]\n\n'
    text+=f'column_blocks_part suffix from {full} start {stop} stop {len(blocks)}\n\n'
    text+='noncomputable def originals : List (List Setup.Block) := ['+', '.join(original(k) for k in range(count))+']\n\n'
    text+='noncomputable def targets : List (List Setup.Block) := ['+', '.join(target(k) for k in range(count))+']\n\n'
    text+=f'column_parts_cover sourceCoverage from {full} parts ['+', '.join(original(k) for k in range(count))+', suffix]\n\n'
    text+=f'theorem sourceShape : {full}.blocks.toList = originals.flatten ++ suffix := by\n  apply sourceCoverage.trans\n  simp only [originals, List.flatten_cons, List.flatten_nil, '+('List.append_assoc, ' if count>1 else '')+'List.append_nil]\n\n'
    proof='List.Forall₂.nil'
    for k in reversed(range(count)):
        p=f'chunkAgreement{k}' if k in equal else ns(k)+'.chunkAgreement'
        proof=f'List.Forall₂.cons {p} ({proof})'
    text+='theorem chunksChecked : List.Forall₂ blockChunkAgreement originals targets :=\n  '+proof+'\n\n'
    cols=[];all_parts=[]
    for r,region in enumerate(artifact['tables']):
        col=f'(UnifiedReduced.Setup.{DATA[region["id"]]}.columns[({column} : Nat)])';cols.append(col);pieces=[]
        for k in range(count):
            first=k*CHUNK;last=min(first+CHUNK,stop)
            entries=[(i,j,e) for i in range(first,last) for j,e in enumerate(groups[i]) if e['region']==r]
            if not entries:continue
            if k in equal:pieces.append((f'{ns(k)}.target{k}Region{r}',sum(__import__('gkr_rom_columns').length(e['block']) for i,j,e in entries)))
            else:pieces += [(f'{ns(k)}.part{i}_{j}',__import__('gkr_rom_columns').length(e['block'])) for i,j,e in entries]
        text+=f'column_parts_cover regionShape{r} from {col} parts ['+', '.join(p for p,l in pieces)+']\n\n'
        for j,(piece,size) in enumerate(pieces):
            text+=f'theorem region{r}PartLength{j} : ({piece}.map Setup.Block.length).sum = {size} := by decide +kernel\n\n'
        text+=f'theorem regionLength{r} : ({col}.blocks.toList.map Setup.Block.length).sum = {region["length"]} := by\n  rw [regionShape{r}]\n'
        text+='  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, '+', '.join(f'region{r}PartLength{j}' for j in range(len(pieces)))+']\n  rfl\n\n'
    extras=[f'{ns(i//CHUNK)}.part{i}_{j}' for i,group in enumerate(groups) for j,e in enumerate(group) if e['region'] is None]
    text+='noncomputable def regionBlocks : List Setup.Block := '+' ++ '.join(c+'.blocks.toList' for c in cols)+'\n\n'
    text+='noncomputable def extra : List Setup.Block := '+(' ++ '.join(extras) or '[]')+'\n\n'
    defs=['extra','targets']
    for k in range(count):
        defs.append(target(k))
        if k in special:
            defs.append(ns(k)+'.targets')
            defs += [ns(k)+f'.target{i}' for i in range(k*CHUNK,min((k+1)*CHUNK,stop))]
    text+='theorem targetShape : regionBlocks ++ extra = targets.flatten := by\n  rw [regionBlocks, '+', '.join(f'regionShape{r}' for r in range(16))+']\n'
    text+='  simp only ['+', '.join(defs)+', List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]\n\n'
    text+=f'theorem regionTotal : (regionBlocks.map Setup.Block.length).sum = {PREFIX} := by\n  simp only [regionBlocks, List.map_append, List.sum_append, '+', '.join(f'regionLength{r}' for r in range(16))+']\n\n'
    text+=f'theorem originalLength : (originals.flatten.map Setup.Block.length).sum = {positions[stop]} := by\n'
    text+='  simp only [originals, List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil]\n'
    # Each source block chunk is small even when its column has many thousands of blocks.
    for k in range(count):
        first=k*CHUNK;last=min(first+CHUNK,stop)
        proof=f'{ns(k)}.chunkLength{k}' if k in equal else f'Airbender.Compiler.UnifiedSpecialLengths.Column{column}.Chunk{k}.originalLength'
        text+=f'  have len{k} : ({original(k)}.map Setup.Block.length).sum = {positions[last]-positions[first]} := {proof}\n'
    text+='  rw ['+', '.join(f'len{k}' for k in range(count))+']\n  rfl\n\n'
    text+=f'theorem prefix_value (index : Fin {PREFIX}) : {full}.get? index.val = Setup.getFromBlocks regionBlocks index.val := by\n'
    text+=f'  change Setup.getFromBlocks {full}.blocks.toList index.val = _\n  rw [sourceShape, getFromBlocks_before_suffix _ _ index.val (by rw [originalLength]; have := index.isLt; omega), block_chunks_agree originals targets chunksChecked, ← targetShape]\n  exact getFromBlocks_before_suffix regionBlocks extra index.val (by rw [regionTotal]; exact index.isLt)\n\nend '+owner+'\n'
    return name,text


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--column',type=int,choices=[0,2,3,4,5,6,7,8,9],action='append')
    parser.add_argument('--stage',choices=['special','column'],default='special')
    for flag in ['write','check','build']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args()
    for col in args.column or [0,2,3,4,5,6,7,8,9]:
        generated=special_chunks(col) if args.stage=='special' else [column_module(col)]
        for name,text in generated:
            path=LEAN/(name.replace('.','/')+'.lean')
            if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('unified prefix assembly scaffold changed: '+name)
            if args.write and (not path.exists() or path.read_text()!=text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
            print(name,flush=True)
            if args.build:subprocess.run(['lake','--no-cache','build','+'+name+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)


if __name__=='__main__':main()
