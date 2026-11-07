#!/usr/bin/env python3
"""Generate complete fixed special-span captures for unified columns."""
import argparse
import re
import subprocess
from gkr_unified_prefix import LEAN, plans, CHUNK
from gkr_unified_special_chunks import legacy_modules

COLUMNS=(2,3,4,5,6,7)


def capture_plan(column):
    artifact,blocks,positions,stop,groups,regions=plans(column)
    chosen=[];excluded=[];chunks=[]
    for first in range(0,stop,CHUNK):
        last=min(first+CHUNK,stop)
        if all(entry['mode']=='identical' for group in groups[first:last] for entry in group):continue
        chunks.append(first//CHUNK)
        for index in range(first,last):
            ids={None if entry['region'] is None else artifact['tables'][entry['region']]['id'] for entry in groups[index]}
            (excluded if None in ids or 34 in ids else chosen).append(index)
    return artifact,groups,chunks,chosen,excluded


def dependencies(column,chunk=None):
    _,_,_,_,excluded=capture_plan(column)
    retained={f'Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column{column}.Chunk{index//CHUNK}.Part{(index%CHUNK)//8}'
              for index in excluded if chunk is None or index//CHUNK==chunk}
    return [f'Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column{column}.Projected']+sorted(retained)


def preflight(generated):
    for name,source in generated:
        path=LEAN/(name.replace('.','/')+'.lean')
        if path.exists() and path.read_text()!=source and subprocess.run(
                ['git','ls-files','--error-unmatch',str(path.relative_to(LEAN))],cwd=LEAN,
                stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode:
            raise ValueError('refuse to replace untracked special-span source: '+str(path))


def modules(column,include_legacy=False):
    artifact,groups,chunks,chosen,excluded=capture_plan(column)
    if not chosen:raise ValueError('the fixed special-span scope is empty')
    stem=f'Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column{column}'
    owner=f'Airbender.Compiler.UnifiedFixedSpans.Column{column}'
    source_owner=lambda index:f'Airbender.Compiler.UnifiedSpecialChunks.Column{column}.Chunk{index//CHUNK}'
    foundations=[];foundation_sources=[];data_parts=[];retained=[]
    for name,source in legacy_modules(column):
        if name.endswith('.Foundation'):
            foundations.append(name)
            foundation_sources.append((name,source))
            continue
        namespace=re.search(r'^namespace (\S+)',source,re.M)[1]
        start=source.index('noncomputable def source')
        body=source[start:source.rindex('end '+namespace)]
        sections=re.split(r'(?=noncomputable def source\d+ : Setup.Block)',body)
        data=[];proofs=[]
        for section in sections:
            if not section.strip():continue
            index=int(re.match(r'noncomputable def source(\d+)',section)[1])
            marker=re.search(r'(?:set_option maxHeartbeats \d+ in\n)?theorem follows\d+ :',section)
            if marker is None:raise ValueError('legacy special source boundary changed')
            data.append(section[:marker.start()])
            if index in excluded:proofs.append(section[marker.start():])
        data_parts.append('namespace '+namespace+'\nopen Airbender Airbender.Compiler\n\n'+''.join(data)+'end '+namespace+'\n\n')
        if proofs:
            header=source[:start]
            retained.append((name,f'import {stem}.Projected\n'+header+''.join(proofs)+'end '+namespace+'\n'))
    header=(f'namespace {owner}\nopen Airbender Airbender.Compiler\nopen PackedSetupEquality\n'
            'set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 131072\n\n')
    data=''.join('import '+name+'\n' for name in foundations)+'\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 131072\n\n'+''.join(data_parts)
    if include_legacy:yield from foundation_sources
    yield stem+'.Data',data.rstrip()+'\n'

    codes=(f'import {stem}.Data\nimport Airbender.Import.PackedSetupEmbed\n'
           'import Airbender.Proofs.GKRProtocol.PackedSetupSpans\n\n'+header+
           '-- Import all fixed requests in one command. Cache each verified region.\n'
           'set_option maxHeartbeats 4000000\n\n'
           'import_setup_code_capture from "artifacts/setup/unified.json" [\n')
    specs=[]
    for index in chosen:
        packing='packed_region 54' if column==2 else 'unpacked'
        specs.append(f'  source{index} := column {column} block_start {index} block_count 1 {packing}')
        for target,entry in enumerate(groups[index]):
            region=artifact['tables'][entry['region']]['id']
            if region==34:raise ValueError('program ROM entered fixed scope')
            packed=int(column==2 and region==54)
            specs.append(f'  target{index}_{target} := region {region} column {column} block_start {entry["target"]} block_count 1 packed_bytes {packed}')
    codes+=',\n'.join(specs)+']\n\n'
    for index in chosen:
        codes+=f'def targets{index} : List BlockCode := '+' ++ '.join(f'target{index}_{target}' for target in range(len(groups[index])))+'\n'
    codes+='\ndef requests : List PackedSetupSpans.Request := [\n  '+',\n  '.join(
        f'⟨source{index}.get ⟨0, by decide +kernel⟩, targets{index}⟩' for index in chosen)+']\n\nend '+owner+'\n'
    yield stem+'.Codes',codes

    bindings=f'import {stem}.Codes\nimport Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n'+header
    for index in chosen:
        original=source_owner(index)
        bindings+=(f'numeric_data_binding source{index}_binding : {original}.source{index} = (source{index}.get ⟨0, by decide +kernel⟩).decode\n'
                   f'numeric_data_binding targets{index}_binding : {original}.target{index} = targets{index}.map BlockCode.decode\n')
    bindings+='\nend '+owner+'\n'
    yield stem+'.Bindings',bindings

    certificate=(f'import {stem}.Bindings\n\n'+header+
                 'theorem checked : PackedSetupSpans.check requests = true := by decide +kernel\n\n'
                 'theorem facts (index : Fin requests.length) : PackedSetupSpans.Fact (requests.get index) :=\n'
                 '  PackedSetupSpans.check_sound_at requests checked index\n\nend '+owner+'\n')
    yield stem+'.Certificate',certificate

    projected=f'import {stem}.Certificate\n\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 131072\n\n'
    for chunk in chunks:
        namespace=source_owner(chunk*CHUNK)
        projected+='namespace '+namespace+'\nopen Airbender Airbender.Compiler\n\n'
        for ordinal,index in enumerate(chosen):
            if index//CHUNK!=chunk:continue
            fact=(f'PackedSetupSpans.check_sound_bound_at {owner}.requests {owner}.checked '
                  f'⟨{ordinal}, by decide +kernel⟩ source{index} target{index} '
                  f'{owner}.source{index}_binding {owner}.targets{index}_binding')
            projected+=(f'theorem follows{index} : blockTargetsFollow source{index} 0 target{index} :=\n  ({fact}).2\n\n'
                        f'theorem length{index} : (target{index}.map Setup.Block.length).sum = source{index}.length :=\n  ({fact}).1\n\n')
        projected+='end '+namespace+'\n\n'
    yield stem+'.Projected',projected.rstrip()+'\n'
    if include_legacy:yield from retained


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--column',type=int,choices=COLUMNS,action='append')
    parser.add_argument('--write',action='store_true')
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    for column in args.column or COLUMNS:
        generated=list(modules(column))
        if args.write:preflight(generated)
        for name,source in generated:
            path=LEAN/(name.replace('.','/')+'.lean')
            if args.check and (not path.exists() or path.read_text()!=source):
                raise ValueError('fixed special-span capture changed: '+name)
            if args.write and (not path.exists() or path.read_text()!=source):
                path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
            print(name)


if __name__=='__main__':main()
