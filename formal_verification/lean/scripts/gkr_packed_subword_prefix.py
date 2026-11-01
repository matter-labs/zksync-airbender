#!/usr/bin/env python3
"""Generate complete checks for wholly fixed Subword source groups."""
import argparse
import json
import re
from gkr_subword_prefix import LEAN, legacy_modules, PREFIX
from gkr_shift_prefix_instances import plans
from gkr_packed_rotate_boundary import preflight

COLUMNS=(0,1,2,8)
COUNTS={0:5,1:12,2:6,8:5}


def capture_plan(column):
    artifact=json.loads((LEAN/'artifacts/setup/subword-memory.json').read_text())
    if [region['id'] for region in artifact['tables'][:5]]!=[0,29,30,42,43]:
        raise ValueError('fixed Subword table scope changed')
    _,chunks=plans(artifact,column,prefix=PREFIX,chunk_size=1)
    chosen=[index for index,chunk in enumerate(chunks) if all(kind<5 for kind,_,_ in chunk[-1])]
    if len(chosen)!=COUNTS[column]:raise ValueError('fixed Subword source scope changed')
    return artifact,chunks,chosen


def modules(column):
    artifact,chunks,chosen=capture_plan(column)
    originals=legacy_modules(column)
    stem=f'Airbender.Proofs.GKRProtocol.SubwordFixedChecks.Column{column}'
    owner=f'Airbender.Compiler.SubwordFixedChecks.Column{column}'
    legacy=f'Airbender.Compiler.SubwordPrefixNative.Column{column}'
    parts=[]
    for name,source in originals[:-1]:
        start=source.index('column_blocks_part original')
        sections=re.split(r'(?=column_blocks_part original\d+ from)',source[start:source.rindex('end '+legacy)])
        body='';fixed_only=True
        for section in sections:
            if not section.strip():continue
            index=int(re.match(r'column_blocks_part original(\d+)',section)[1])
            boundary=section.index(f'theorem chunkChecked{index}')
            body+=section[:boundary] if index in chosen else section
            fixed_only=fixed_only and index in chosen
        parts.append(name)
        imports=source[:start]
        if fixed_only:imports=re.sub(r'^set_option maxHeartbeats \d+\n','',imports,flags=re.M)
        yield name,imports+body+'end '+legacy+'\n'

    header=(f'namespace {owner}\nopen Airbender Airbender.Compiler\n'
            'open PackedSetupEquality PackedSetupNormalization\nset_option warningAsError true\n'
            'set_option Elab.async false\nset_option maxRecDepth 8192\n\n')
    capture=(''.join('import '+part+'\n' for part in parts)+
             'import Airbender.Import.PackedSetupEmbed\n'
             'import Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n'
             'import Airbender.Proofs.GKRProtocol.PackedSetupNormalization\n\n'+header+
             '-- Each request stays inside the five fixed regions.\n'
             'import_setup_code_capture from "artifacts/setup/subword-memory.json" [\n')
    specs=[]
    for index in chosen:
        first,last,_,_,selected=chunks[index]
        specs.append(f'  source{index} := column {column} block_start {first} block_count {last-first} unpacked')
        for kind,start,end in selected:
            if kind>=5:raise ValueError('program ROM entered fixed Subword scope')
            specs.append(f'  target{index}Region{kind} := region {artifact["tables"][kind]["id"]} column {column} block_start {start} block_count {end-start} packed_bytes 0')
    capture+=',\n'.join(specs)+']\n\n'
    for index in chosen:
        selected=chunks[index][-1]
        targets=' ++ '.join(f'target{index}Region{kind}' for kind,_,_ in selected)
        capture+=f'def targets{index} : List BlockCode := {targets}\n'
        capture+=(f'numeric_data_binding source{index}_binding : {legacy}.original{index} = source{index}.map BlockCode.decode\n'
                  f'numeric_data_binding target{index}_binding : {legacy}.target{index} = targets{index}.map BlockCode.decode\n\n')
    capture+='def requests : List Request := [\n  '+',\n  '.join(
        f'⟨source{index}, targets{index}, {chunks[index][3]-chunks[index][2]}⟩' for index in chosen)+']\n\n'
    capture+=('theorem checked : PackedSetupNormalization.check requests = true := by decide +kernel\n\n'
              'theorem facts (index : Fin requests.length) : Fact (requests.get index) :=\n'
              '  PackedSetupNormalization.check_sound_at requests checked index\n\nend '+owner+'\n\n')
    capture+=(f'namespace {legacy}\nopen Airbender Airbender.Compiler\n'
              'set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 8192\n\n')
    for ordinal,index in enumerate(chosen):
        capture+=(f'theorem chunkChecked{index} : normalizeSetupBlocks original{index} = normalizeSetupBlocks target{index} := by\n'
                  f'  rw [{owner}.source{index}_binding, {owner}.target{index}_binding]\n'
                  f'  exact ({owner}.facts ⟨{ordinal}, by decide +kernel⟩).1\n\n'
                  f'theorem chunkLength{index} : (original{index}.map Setup.Block.length).sum = {chunks[index][3]-chunks[index][2]} := by\n'
                  f'  rw [{owner}.source{index}_binding]\n'
                  f'  exact ({owner}.facts ⟨{ordinal}, by decide +kernel⟩).2\n\n')
    yield stem,capture+'end '+legacy+'\n'
    name,source=originals[-1]
    yield name,'import '+stem+'\n'+source


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--column',type=int,choices=COLUMNS,action='append')
    parser.add_argument('--write',action='store_true');parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    for column in args.column or COLUMNS:
        generated=list(modules(column))
        if args.write:preflight(generated)
        for name,source in generated:
            path=LEAN/(name.replace('.','/')+'.lean')
            if args.check and (not path.exists() or path.read_text()!=source):raise ValueError('complete fixed Subword capture changed: '+name)
            if args.write and (not path.exists() or path.read_text()!=source):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
            print(name)


if __name__=='__main__':main()
