#!/usr/bin/env python3
"""Check fixed unified region-part lengths through numeric capture views."""
import argparse
from gkr_unified_prefix import LEAN, plans, CHUNK
from gkr_unified_equal_chunks import PACKED_COLUMNS, TREE_COLUMNS
from gkr_packed_special_spans import capture_plan
from gkr_packed_rotate_boundary import preflight
from gkr_rom_columns import length

COLUMNS=(2,3,4,5,6,7)


def metadata_plan(column):
    artifact,_,_,stop,groups,_=plans(column)
    chosen=set(capture_plan(column)[3]);equal={};offset=0
    for start in range(0,stop,CHUNK):
        end=min(start+CHUNK,stop)
        if all(entry['mode']=='identical' for group in groups[start:end] for entry in group):
            equal[start//CHUNK]=offset;offset+=end-start
    result=[]
    for region,table in enumerate(artifact['tables']):
        if table['id']==34:continue
        part=0
        for start in range(0,stop,CHUNK):
            end=min(start+CHUNK,stop);chunk=start//CHUNK
            entries=[(i,j,entry) for i in range(start,end) for j,entry in enumerate(groups[i]) if entry['region']==region]
            if chunk in equal and entries:
                capture='Airbender.Compiler.'+PACKED_COLUMNS[column][2]
                prior=sum(1 for group in groups[start:end] for entry in group if entry['region']<region)
                first=equal[chunk]+prior;size=len(entries)
                expected=PACKED_COLUMNS[column][3][table['id']]+entries[0][2]['target']
                if expected!=first:raise ValueError('fixed equal region position changed')
                view=(f'(({capture}.targetTree.chunk {equal[chunk]}).drop {prior}).take {size}' if column in TREE_COLUMNS else
                      f'({capture}.targetCode.drop {first}).take {size}')
                result.append(dict(region=region,part=part,kind='equal',piece=f'Airbender.Compiler.UnifiedEqualChunks.Column{column}.target{chunk}Region{region}',
                    rows=sum(length(entry['block']) for _,_,entry in entries),view=view))
                part+=1
            elif chunk not in equal:
                for index,target,entry in entries:
                    owner=f'Airbender.Compiler.UnifiedFixedSpans.Column{column}'
                    result.append(dict(region=region,part=part,kind='known' if index in chosen else 'extra',
                        piece=f'Airbender.Compiler.UnifiedSpecialChunks.Column{column}.Chunk{chunk}.part{index}_{target}',rows=length(entry['block']),
                        view=f'{owner}.target{index}_{target}',index=index,target=target,table=table['id'],block=entry['target']))
                    part+=1
    return result


def modules(column):
    entries=metadata_plan(column)
    stem=f'Airbender.Proofs.GKRProtocol.UnifiedRegionLengths.Column{column}'
    owner=f'Airbender.Compiler.UnifiedRegionLengths.Column{column}'
    header=(f'namespace {owner}\nopen Airbender Airbender.Compiler\nopen PackedSetupEquality PackedSetupLengths\n'
            'set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 8192\n\n')
    data=f'import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column{column}.Bindings\n'
    if column in PACKED_COLUMNS:data+=f'import Airbender.Proofs.GKRProtocol.UnifiedEqualParts.Column{column}.Projected\n'
    data+=('import Airbender.Import.PackedSetupEmbed\nimport Airbender.Proofs.GKRProtocol.PackedSetupLengths\n\n'+header)
    extras=[(ordinal,entry) for ordinal,entry in enumerate(entries) if entry['kind']=='extra']
    if extras:
        data+='-- Import only fixed target pieces that have no existing numeric view.\n'
        data+='import_setup_code_capture from "artifacts/setup/unified.json" [\n'+',\n'.join(
            f'  extra{ordinal} := region {entry["table"]} column {column} block_start {entry["block"]} block_count 1 packed_bytes {int(column==2 and entry["table"]==54)}'
            for ordinal,entry in extras)+']\n\n'
    bindings=f'import {stem}.Data\nimport Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n'+header
    for ordinal,entry in enumerate(entries):
        view=f'extra{ordinal}' if entry['kind']=='extra' else entry['view']
        data+=f'noncomputable def view{ordinal} : List BlockCode := {view}\n'
        binding=f'{entry["piece"]} = view{ordinal}.map BlockCode.decode'
        if entry['kind']=='known':
            bindings+=(f'theorem binding{ordinal} : {binding} :=\n'
                     f'  congrArg (fun blocks : List Setup.Block => (blocks.drop {entry["target"]}).take 1) '
                     f'Airbender.Compiler.UnifiedFixedSpans.Column{column}.targets{entry["index"]}_binding\n\n')
        else:bindings+=f'numeric_data_binding binding{ordinal} : {binding}\n\n'
    data+='\n-- These views support kernel proofs. They do not need runtime compilation.\n'
    data+='noncomputable def requests : List Request := [\n  '+',\n  '.join(
        f'⟨view{ordinal}, {entry["rows"]}⟩' for ordinal,entry in enumerate(entries))+']\n\n'
    yield stem+'.Data',data+'end '+owner+'\n'
    yield stem+'.Bindings',bindings+'end '+owner+'\n'
    yield stem+'.Certificate',(f'import {stem}.Bindings\n\n'+header+
        'theorem checked : PackedSetupLengths.check requests = true := by decide +kernel\n\n'
        'theorem facts (index : Fin requests.length) : Fact (requests.get index) :=\n'
        '  PackedSetupLengths.check_sound_at requests checked index\n\nend '+owner+'\n')
    projected=f'import {stem}.Certificate\n\n'+header
    for ordinal,entry in enumerate(entries):
        projected+=(f'theorem length{ordinal} : ({entry["piece"]}.map Setup.Block.length).sum = {entry["rows"]} := by\n'
                 f'  rw [binding{ordinal}]\n  exact facts ⟨{ordinal}, by decide +kernel⟩\n\n')
    yield stem,projected+'end '+owner+'\n'


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--column',type=int,choices=COLUMNS,action='append')
    parser.add_argument('--write',action='store_true');parser.add_argument('--check',action='store_true');args=parser.parse_args()
    for column in args.column or COLUMNS:
        generated=list(modules(column))
        if args.write:preflight(generated)
        for name,source in generated:
            path=LEAN/(name.replace('.','/')+'.lean')
            if args.check and (not path.exists() or path.read_text()!=source):raise ValueError('fixed unified region lengths changed: '+name)
            if args.write and (not path.exists() or path.read_text()!=source):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
            print(name)


if __name__=='__main__':main()
