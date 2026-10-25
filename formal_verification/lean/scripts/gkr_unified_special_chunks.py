#!/usr/bin/env python3
"""Generate bounded span certificates for changed unified prefix chunks."""
import argparse
import os
import subprocess
from export_gkr_translations import LEAN
from gkr_unified_prefix import plans,pilot,CHUNK


def modules(column):
    artifact,blocks,positions,stop,groups,regions=plans(column)
    for first in range(0,stop,CHUNK):
        last=min(first+CHUNK,stop)
        if all(e['mode']=='identical' for group in groups[first:last] for e in group):continue
        chunk=first//CHUNK
        owner=f'Airbender.Compiler.UnifiedSpecialChunks.Column{column}.Chunk{chunk}'
        prefix=f'GKRProtocol.UnifiedSpecialParts.Column{column}.Chunk{chunk}'
        _,text=pilot(column,first,first,assemble=True,source_start=first,source_end=last,namespace=owner)
        text=text[:text.index('noncomputable def sources')]+'end '+owner+'\n'
        text='\n'.join(line for line in text.split('\n') if not line.startswith('column_blocks_part suffix '))
        yield prefix+'.Foundation',text
        for begin in range(first,last,8):
            _,text=pilot(column,begin,min(begin+8,last),assemble=False,source_start=first,source_end=last,namespace=owner,foundation_module=prefix+'.Foundation')
            yield prefix+f'.Part{(begin-first)//8}',text


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--column',type=int,choices=[0,2,3,4,5,6,7,8,9],action='append')
    for flag in ['write','check','build']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args()
    for column in args.column or [0,2,3,4,5,6,7,8,9]:
        for name,text in modules(column):
            path=LEAN/(name.replace('.','/')+'.lean')
            if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('unified changed span scaffold changed: '+name)
            if args.write and (not path.exists() or path.read_text()!=text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
            print(name,flush=True)
            if args.build:subprocess.run(['lake','--no-cache','build','+'+name+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)


if __name__=='__main__':main()
