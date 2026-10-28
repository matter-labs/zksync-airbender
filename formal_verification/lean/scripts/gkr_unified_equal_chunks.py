#!/usr/bin/env python3
"""Check unchanged unified prefix chunks against independently imported regions."""
import argparse
import os
import subprocess
from export_gkr_translations import LEAN
from gkr_unified_prefix import plans,DATA,CHUNK

PER_MODULE=4


def modules(column):
    artifact,blocks,positions,stop,groups,regions=plans(column)
    selected=[]
    for first in range(0,stop,CHUNK):
        last=min(first+CHUNK,stop)
        if all(e['mode']=='identical' for group in groups[first:last] for e in group):selected.append((first,last))
    for begin in range(0,len(selected),PER_MODULE):
        name=f'Airbender.Proofs.GKRProtocol.UnifiedEqualParts.Column{column}.Part{begin//PER_MODULE}'
        ns=f'Airbender.Compiler.UnifiedEqualChunks.Column{column}'
        text=('import Airbender.Import.GKRProtocol.BlockPartsImport\nimport Airbender.Data.GKRSetup.Unified\n'
          'import Airbender.Data.Setup.UnifiedReduced.NativeFixedData\nimport Airbender.Data.Setup.UnifiedReduced.Native.ROMData\n\nnamespace '+ns+'\n'
          'open Airbender Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n')
        for first,last in selected[begin:begin+PER_MODULE]:
            i=first//CHUNK
            text+=f'column_blocks_part original{i} from Data.GKRSetup.Unified.setupColumn{column} start {first} stop {last}\n'
            names=[]
            for r,region in enumerate(artifact['tables']):
                entries=[e for group in groups[first:last] for e in group if e['region']==r]
                if not entries:continue
                indexes=[e['target'] for e in entries];assert indexes==list(range(indexes[0],indexes[-1]+1))
                part=f'target{i}Region{r}';names.append(part)
                text+=f'column_blocks_part {part} from (UnifiedReduced.Setup.{DATA[region["id"]]}.columns[({column} : Nat)]) start {indexes[0]} stop {indexes[-1]+1}\n'
            text+=f'noncomputable def target{i} : List Setup.Block := '+' ++ '.join(names)+'\n\n'
            text+=f'theorem chunkSame{i} : original{i} = target{i} := by rfl\n\n'
            text+=f'theorem chunkLength{i} : (original{i}.map Setup.Block.length).sum = {positions[last]-positions[first]} := by decide +kernel\n\n'
        text+='end '+ns+'\n';yield name,text


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--column',type=int,choices=range(10),action='append')
    for flag in ['write','check','build']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args()
    for col in args.column or range(10):
        for name,text in modules(col):
            path=LEAN/(name.replace('.','/')+'.lean')
            if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('unified equality scaffold changed: '+name)
            if args.write and (not path.exists() or path.read_text()!=text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
            print(name,flush=True)
            if args.build:subprocess.run(['lake','--no-cache','build','+'+name+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)


if __name__=='__main__':main()
