#!/usr/bin/env python3
"""Generate one complete capture for the remaining fixed column-one spans."""
import argparse
import re
import subprocess
from gkr_unified_prefix import LEAN, pilot, plans
from gkr_packed_rotate_boundary import preflight

STEM='Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column1'
OWNER='Airbender.Compiler.UnifiedFixedSpans.Column1'
LEGACY='Airbender.Compiler.UnifiedPrefixNative.Column1'
PARTS='Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1'


def capture_plan():
    artifact,_,_,stop,groups,_=plans(1)
    fixed=[];excluded=[]
    for index,group in enumerate(groups):
        ids={None if entry['region'] is None else artifact['tables'][entry['region']]['id'] for entry in group}
        (excluded if None in ids or 34 in ids else fixed).append(index)
    if stop!=34 or excluded!=[12,13,33] or 14 not in fixed:
        raise ValueError('fixed column-one scope changed')
    return artifact,groups,[index for index in fixed if index!=14]


def modules():
    artifact,groups,chosen=capture_plan()
    header=(f'namespace {OWNER}\nopen Airbender Airbender.Compiler\nopen PackedSetupEquality\n'
            'set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 131072\n\n')
    data=(f'import {PARTS}.Foundation\n\nnamespace {LEGACY}\nopen Airbender Airbender.Compiler\n'
          'set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\n\n')
    for index in chosen:
        _,old=pilot(1,index,index+1,assemble=False)
        start=old.index('noncomputable def source')
        stop=re.search(r'(?:set_option maxHeartbeats \d+ in\n)?theorem follows\d+ :',old).start()
        data+=old[start:stop]
    yield STEM+'.Data',data.rstrip()+'\n\nend '+LEGACY+'\n'

    codes=(f'import {STEM}.Data\nimport Airbender.Import.PackedSetupEmbed\n'
           'import Airbender.Proofs.GKRProtocol.PackedSetupSpans\n\n'+header+
           'set_option maxHeartbeats 2000000\n\n'
           'import_setup_code_capture from "artifacts/setup/unified.json" [\n')
    specs=[]
    for index in chosen:
        specs.append(f'  source{index} := column 1 block_start {index} block_count 1 unpacked')
        for target,entry in enumerate(groups[index]):
            region=artifact['tables'][entry['region']]['id']
            specs.append(f'  target{index}_{target} := region {region} column 1 block_start {entry["target"]} block_count 1 packed_bytes 0')
    codes+=',\n'.join(specs)+']\n\n'
    for index in chosen:
        codes+=f'def targets{index} : List BlockCode := '+' ++ '.join(f'target{index}_{target}' for target in range(len(groups[index])))+'\n'
    codes+='\ndef requests : List PackedSetupSpans.Request := [\n  '+',\n  '.join(
        f'⟨source{index}.get ⟨0, by decide +kernel⟩, targets{index}⟩' for index in chosen)+']\n\nend '+OWNER+'\n'
    yield STEM+'.Codes',codes

    bindings=f'import {STEM}.Codes\nimport Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n'+header
    for index in chosen:
        bindings+=(f'numeric_data_binding source{index}_binding : {LEGACY}.source{index} = (source{index}.get ⟨0, by decide +kernel⟩).decode\n'
                   f'numeric_data_binding targets{index}_binding : {LEGACY}.target{index} = targets{index}.map BlockCode.decode\n')
    yield STEM+'.Bindings',bindings+'\nend '+OWNER+'\n'
    yield STEM+'.Certificate',(f'import {STEM}.Bindings\n\n'+header+
        'theorem checked : PackedSetupSpans.check requests = true := by decide +kernel\n\nend '+OWNER+'\n')

    projected=(f'import {STEM}.Certificate\n\nnamespace {LEGACY}\nopen Airbender Airbender.Compiler\n'
               'set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 131072\n\n')
    for ordinal,index in enumerate(chosen):
        fact=(f'PackedSetupSpans.check_sound_bound_at {OWNER}.requests {OWNER}.checked '
              f'⟨{ordinal}, by decide +kernel⟩ source{index} target{index} '
              f'{OWNER}.source{index}_binding {OWNER}.targets{index}_binding')
        projected+=(f'theorem follows{index} : blockTargetsFollow source{index} 0 target{index} :=\n  ({fact}).2\n\n'
                    f'theorem length{index} : (target{index}.map Setup.Block.length).sum = source{index}.length :=\n  ({fact}).1\n\n')
    yield STEM+'.Projected',projected+'end '+LEGACY+'\n'


def obsolete():
    return [path for path in (LEAN/PARTS.replace('.','/')).glob('*.lean')
            if path.stem=='Part0' or path.stem.startswith('Unit') and int(path.stem[4:]) not in [12,13,14,33]]


def prepare(generated,write=False,check=False):
    retired=obsolete()
    if check and retired:raise ValueError('obsolete fixed column-one proof shards remain')
    if write:
        preflight(generated)
        for path in retired:
            if subprocess.run(['git','ls-files','--error-unmatch',str(path.relative_to(LEAN))],cwd=LEAN,
                              stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode:
                raise ValueError('refuse to delete untracked column-one source: '+str(path))
    return retired


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true');parser.add_argument('--check',action='store_true')
    args=parser.parse_args();generated=list(modules())
    retired=prepare(generated,args.write,args.check)
    for name,source in generated:
        path=LEAN/(name.replace('.','/')+'.lean')
        if args.check and (not path.exists() or path.read_text()!=source):raise ValueError('fixed column-one capture changed: '+name)
        if args.write and (not path.exists() or path.read_text()!=source):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
        print(name)
    if args.write:
        for path in retired:path.unlink()


if __name__=='__main__':main()
