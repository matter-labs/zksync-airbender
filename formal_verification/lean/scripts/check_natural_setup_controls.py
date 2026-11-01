#!/usr/bin/env python3
"""Require kernel rejection of altered fixed Subword setup codes."""
from pathlib import Path
import json
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[1]
PREFIX='''import Tests.PackedSubwordCodes
open Airbender Airbender.Compiler PackedSetupEquality
namespace NaturalSetupControl
'''


def main():
    artifact=json.loads((ROOT/'artifacts/setup/subword-memory.json').read_text())
    if [region['id'] for region in artifact['tables'][:5]]!=[0,29,30,42,43]:
        raise SystemExit('fixed Subword table scope changed')
    fixed_end=artifact['tables'][5]['offset']
    for index,(column,block) in enumerate([(1,2),(1,8),(1,11),(2,3)]):
        sizes=[entry.get('length',len(entry.get('values',[]))*entry.get('repetitions',1))
               for entry in artifact['columns'][column]['blocks']]
        if sum(sizes[:block+1])>fixed_end:
            raise SystemExit('program ROM entered the fixed setup controls')
        source=f'(Data.GKRSetup.SubwordMemory.setupColumn{column}.blocks.toList.drop {block}).take 1'
        exact=f'{source} = Tests.PackedSubwordCodes.codes{index}.map BlockCode.decode'
        changed=f'{source} = [BlockCode.decode (.affine 65536 0 0)]'
        for mutated,statement in [(False,exact),(True,changed)]:
            with tempfile.TemporaryDirectory(prefix='airbender-natural-setup-') as directory:
                path=Path(directory)/'Check.lean'
                path.write_text(PREFIX+f'numeric_data_binding result : {statement}\nend NaturalSetupControl\n')
                result=subprocess.run(['lean','-j1','-DElab.async=false',str(path)],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            if not mutated and result.returncode:raise SystemExit(f'Exact fixed source {index} failed:\n'+result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit(f'Changed fixed source {index} did not fail in the kernel:\n'+result.stdout[-2000:])
    print('PASS four exact natural setup bindings; kernel rejects all four mutations')


if __name__=='__main__':main()
