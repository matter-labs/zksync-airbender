#!/usr/bin/env python3
"""Check unchanged unified prefix chunks against independently imported regions."""
import argparse
import os
import re
import subprocess
from export_gkr_translations import LEAN
from gkr_unified_prefix import plans,DATA,CHUNK

PER_MODULE=4
PACKED_COLUMNS = {
    2: ('UnifiedPackedEqualityCodes', 'UnifiedPackedEqualityCertificate',
        'UnifiedPackedEquality', {52: -111, 53: 788, 54: 1686}),
    5: ('UnifiedPackedEquality.Column5.Codes', 'UnifiedPackedEquality.Column5.Certificate',
        'UnifiedPackedEquality.Column5', {9: -128, 49: 24304, 50: 25202}),
}



def packed_modules(column, artifact, positions, groups, selected):
    code_module, certificate, capture, region_offsets = PACKED_COLUMNS[column]
    code = (LEAN/('Airbender/Proofs/GKRProtocol/'+code_module.replace('.', '/')+'.lean')).read_text()
    specifications = [tuple(map(int, entry)) for entry in re.findall(r'⟨(\d+), (\d+), (\d+)⟩', code)]
    expected, offset = [], 0
    for first, last in selected:
        expected.append((offset, last - first, positions[last] - positions[first]))
        offset += last - first
    if specifications != expected:
        raise ValueError('fixed column capture scope or row-count statements changed')
    name = f'Airbender.Proofs.GKRProtocol.UnifiedEqualParts.Column{column}.Projected'
    namespace = f'Airbender.Compiler.UnifiedEqualChunks.Column{column}'
    text = (f'import Airbender.Proofs.GKRProtocol.{certificate}\n\n'
            'namespace ' + namespace + '\nopen Airbender Airbender.Compiler\n'
            'set_option warningAsError true\nset_option Elab.async false\n\n')
    if column == 5:
        text += ('-- Each projection reduces one bounded leaf and a tree path.\n'
                 'set_option maxRecDepth 8192\n\n')
    for ordinal, (first, last) in enumerate(selected):
        index = first // CHUNK
        offset, count, rows = specifications[ordinal]
        if column == 5:
            text += (f'noncomputable def original{index} : List Setup.Block :=\n'
                     f'  {capture}.sourceChunk {offset}\n')
        else:
            text += (f'noncomputable def original{index} : List Setup.Block :=\n'
                     f'  ({capture}.sourceBlocks.drop {offset}).take {count}\n')
        names, pieces = [], []
        for region_index, region in enumerate(artifact['tables']):
            entries = [entry for group in groups[first:last] for entry in group if entry['region'] == region_index]
            if not entries:
                continue
            table = region['id']
            if table not in region_offsets:
                raise ValueError('program-dependent region in fixed column capture')
            indexes = [entry['target'] for entry in entries]
            assert indexes == list(range(indexes[0], indexes[-1]+1))
            part = f'target{index}Region{region_index}'
            start = region_offsets[table] + indexes[0]
            size = len(indexes)
            names.append(part)
            pieces.append(size)
            if column == 5:
                prior = sum(pieces[:-1])
                if start != offset + prior:
                    raise ValueError('fixed target chunk position changed')
                leaf = f'({capture}.targetChunk {offset})'
                if prior:
                    value = f'{leaf}.drop {prior}'
                elif size == count:
                    value = leaf
                else:
                    value = f'{leaf}.take {size}'
                text += f'noncomputable def {part} : List Setup.Block := {value}\n'
            else:
                text += (f'noncomputable def {part} : List Setup.Block :=\n'
                         f'  ({capture}.targetBlocks.drop {start}).take {size}\n')
        text += f'noncomputable def target{index} : List Setup.Block := ' + ' ++ '.join(names) + '\n\n'
        text += f'theorem chunkSame{index} : original{index} = target{index} := by\n'
        if column == 5:
            if len(pieces) == 1:
                text += f'  exact {capture}.chunk_eq {offset}\n\n'
            elif len(pieces) == 2:
                text += (f'  exact ({capture}.chunk_eq {offset}).trans\n'
                         f'    (List.take_append_drop {pieces[0]} ({capture}.targetChunk {offset})).symm\n\n')
            else:
                raise ValueError('unexpected fixed column region boundary')
        elif len(pieces) == 1:
            text += f'  exact {capture}.slice_eq {offset} {count}\n\n'
        elif len(pieces) == 2:
            text += (f'  exact ({capture}.slice_eq {offset} {count}).trans\n'
                     f'    (PackedSetupEquality.slice_split {capture}.targetBlocks {offset} {pieces[0]} {pieces[1]})\n\n')
        else:
            raise ValueError('unexpected fixed column region boundary')
        text += f'theorem chunkLength{index} : (original{index}.map Setup.Block.length).sum = {rows} := by\n'
        if column == 5:
            text += f'  exact {capture}.chunk_length_at ⟨{ordinal}, by decide +kernel⟩\n\n'
        else:
            text += f'  exact {capture}.length_at ⟨{ordinal}, by decide +kernel⟩\n\n'
    yield name, text + 'end ' + namespace + '\n'

def modules(column):
    artifact,blocks,positions,stop,groups,regions=plans(column)
    selected=[]
    for first in range(0,stop,CHUNK):
        last=min(first+CHUNK,stop)
        if all(e['mode']=='identical' for group in groups[first:last] for e in group):selected.append((first,last))
    if column in PACKED_COLUMNS:
        yield from packed_modules(column, artifact, positions, groups, selected)
        return
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
        generated = list(modules(col))
        if col in PACKED_COLUMNS:
            for legacy in sorted((LEAN/f'Airbender/Proofs/GKRProtocol/UnifiedEqualParts/Column{col}').glob('Part*.lean')):
                if legacy.exists():
                    if args.check:
                        raise ValueError('obsolete fixed column fact shard: '+str(legacy))
                    if args.write and subprocess.run(
                            ['git', 'ls-files', '--error-unmatch', str(legacy.relative_to(LEAN))],
                            cwd=LEAN, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode:
                        raise ValueError('refuse to delete untracked legacy shard: '+str(legacy))
        for name,text in generated:
            path=LEAN/(name.replace('.','/')+'.lean')
            if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('unified equality scaffold changed: '+name)
            if args.write and (not path.exists() or path.read_text()!=text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
            print(name,flush=True)
            if args.build:subprocess.run(['lake','--no-cache','build','+'+name+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)
        if col in PACKED_COLUMNS and args.write:
            for legacy in sorted((LEAN/f'Airbender/Proofs/GKRProtocol/UnifiedEqualParts/Column{col}').glob('Part*.lean')):
                if legacy.exists():
                    legacy.unlink()


if __name__=='__main__':main()
