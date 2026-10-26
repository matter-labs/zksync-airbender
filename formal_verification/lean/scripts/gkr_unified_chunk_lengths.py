#!/usr/bin/env python3
"""Isolate bounded native source length certificates from column assembly."""
import argparse
from export_gkr_translations import LEAN
from gkr_unified_prefix import plans,CHUNK


def modules(column):
    _,blocks,positions,stop,groups,_=plans(column)
    for first in range(0,stop,CHUNK):
        last=min(first+CHUNK,stop)
        if all(e['mode']=='identical' for group in groups[first:last] for e in group):continue
        chunk=first//CHUNK;owner=f'Airbender.Compiler.UnifiedSpecialLengths.Column{column}.Chunk{chunk}'
        original=f'Airbender.Compiler.UnifiedSpecialChunks.Column{column}.Chunk{chunk}.original'
        name=f'Airbender.Proofs.GKRProtocol.UnifiedSpecialLengths.Column{column}.Chunk{chunk}'
        text=f'import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column{column}.Chunk{chunk}.Foundation\n\nnamespace {owner}\nopen Airbender\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 16000000\n\n'
        if sum(len(block.get('values',[])) for block in blocks[first:last])>4096:
            # Bound reductions of the two large literal-array chunks independently.
            parts=[]
            for begin in range(first,last,16):
                end=min(begin+16,last);part=(begin-first)//16;parts.append(f'part{part}')
                part_name=name+f'Part{part}'
                dependencies=''.join(f'import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column{column}.Chunk{chunk}.Part{k}\n' for k in range((begin-first)//8,(end-first+7)//8))
                part_text=dependencies+text[text.index('\nnamespace '):]
                source_owner=f'Airbender.Compiler.UnifiedSpecialChunks.Column{column}.Chunk{chunk}'
                part_text+=f'open {source_owner}\n\n'
                part_text+=f'noncomputable def part{part} : List Setup.Block := ['+', '.join(f'source{i}' for i in range(begin,end))+']\n\n'
                for i in range(begin,end):
                    part_text+=f'theorem sourceLength{i} : source{i}.length = {positions[i+1]-positions[i]} := length{i}.symm.trans (by rfl)\n\n'
                part_text+=f'theorem partLength{part} : (part{part}.map Setup.Block.length).sum = {positions[end]-positions[begin]} := by\n'
                part_text+=f'  simp only [part{part}, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, '+', '.join(f'sourceLength{i}' for i in range(begin,end))+']; rfl\n\nend '+owner+'\n'
                yield part_name,part_text
            header=''.join(f'import {name}Part{part}\n' for part in range(len(parts)))
            text=header+text[text.index('\nnamespace '):]
            text+='noncomputable def lengthParts : List (List Setup.Block) := ['+', '.join(parts)+']\n\n'
            text+=f'theorem sourceShape : {original} = lengthParts.flatten := by rfl\n\n'
            text+=f'theorem originalLength : ({original}.map Setup.Block.length).sum = {positions[last]-positions[first]} := by\n  rw [sourceShape]\n'
            text+='  simp only [lengthParts, List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, '+', '.join(f'partLength{part}' for part in range(len(parts)))+']; rfl\n\n'
            text+='end '+owner+'\n'
        else:text+=f'theorem originalLength : ({original}.map Setup.Block.length).sum = {positions[last]-positions[first]} := by rfl\n\nend {owner}\n'
        yield name,text


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--column',type=int,choices=[0,2,3,4,5,6,7,8,9],action='append')
    for flag in ['write','check']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args()
    for column in args.column or [0,2,3,4,5,6,7,8,9]:
        for name,text in modules(column):
            path=LEAN/(name.replace('.','/')+'.lean')
            if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('unified chunk length scaffold changed: '+name)
            if args.write and (not path.exists() or path.read_text()!=text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
            print(name)

if __name__=='__main__':main()
