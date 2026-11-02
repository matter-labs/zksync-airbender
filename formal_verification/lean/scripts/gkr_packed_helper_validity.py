#!/usr/bin/env python3
"""Check complete helper erasure, borrow and exact transport obligations."""
import argparse
import hashlib
import json
from export_gkr_translations import LEAN
import gkr_helper_validity_instances as legacy
from gkr_wiring_instances import CASES as STEMS
from export_gkr_translations import FAMILIES
from gkr_packed_functional_steps import balanced
from gkr_packed_worker_ports import merge
from gkr_packed_rotate_boundary import preflight

ALL_CASES=tuple(stem+mode for stem in STEMS for mode in ['Cached','Uncached'])
CASES=tuple(stem+mode for stem in ['AddSub','BlakeRound'] for mode in ['Cached','Uncached'])
DIMENSIONS=LEAN/'artifacts/checkers/helper-validity-dimensions.json'


def capture_name(case):
    for family,stem in zip(FAMILIES,STEMS,strict=True):
        for mode in ['Cached','Uncached']:
            if case==stem+mode:return family+'-'+mode.lower()
    raise ValueError('unknown helper capture: '+case)


def fingerprint(case):
    name=capture_name(case);digest=hashlib.sha256()
    for path in [LEAN/f'artifacts/compiler/{name}.json',LEAN/f'artifacts/compiler/{name}-source.json',
                 LEAN/'scripts/gkr_helper_validity_instances.py',LEAN/'Airbender/Import/GKRProtocol/HelperValidityImport.lean']:
        digest.update(path.relative_to(LEAN).as_posix().encode());digest.update(b'\0');digest.update(path.read_bytes())
    return digest.hexdigest()


def dimensions(case):
    row=json.loads(DIMENSIONS.read_text())[case]
    if row['source_sha256']!=fingerprint(case):raise ValueError('refresh helper source dimensions: '+case)
    return row['protected'],row['fields']


def original(case):
    return legacy.module(capture_name(case),case)[1]


def inputs(case):
    text=original(case);text=text[:text.index('theorem helper_graph_extends')]
    text=text.replace('set_option maxHeartbeats 4000000\n','')
    return text.rstrip()+' phase 0\n\nend Airbender.Compiler.HelperValidityNative.'+case+'\n'


def source(case):
    return (f'NumericHelperValidityChecks.ofTyped Airbender.Compiler.HistoryErasureNative.{case}.native.historyCells\n'
        f'  Airbender.Compiler.HelperValidityNative.{case}.native.profile\n'
        f'  Airbender.Compiler.FullArithmeticNative.{case}.native.helperPlacement Airbender.Compiler.SourceContractNative.{case}.native.slots\n'
        f'  Airbender.Compiler.HelperNative.{case}.native.fields Airbender.Compiler.HelperNative.{case}.native.placement\n'
        f'  Airbender.Compiler.FullArithmeticNative.{case}.native.inputBank Airbender.Compiler.MemoryNative.{case}.native.bank')


def header(case):
    return f'namespace Airbender.Compiler.HelperValidityChecks.{case}\nopen Airbender Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 8192\n\n'


def modules(case):
    protected,fields=dimensions(case)
    shapes=[('protectedFields',protected),('borrows',fields),('transports',fields)]
    stem='Airbender.Proofs.GKRProtocol.HelperValidityChecks.'+case;end='\nend Airbender.Compiler.HelperValidityChecks.'+case+'\n'
    yield stem+'.Inputs',inputs(case)
    yield stem+'.Typed',(f'import {stem}.Inputs\nimport Airbender.Proofs.GKRProtocol.NumericHelperValidityChecks\n\n'+header(case)+'noncomputable def original := '+source(case)+'\n'+end)
    lines=['numeric_helper_validity_capture metadata := ⟨original.coordinates, original.borrowBound, [], [], []⟩\n'];chunks={}
    for field,size in shapes:
        chunks[field]=[]
        for first in range(0,size,4):
            width=min(4,size-first);values={name:'[]' for name,_ in shapes};values[field]=f'(original.{field}.drop {first}).take {width}'
            name=field+str(first);chunks[field].append(name+'.'+field)
            lines.append('numeric_helper_validity_capture '+name+' := ⟨[], 0, '+', '.join(values[name] for name,_ in shapes)+'⟩\n')
    lines.append('noncomputable def data : NumericHelperValidityChecks.Capture :=\n  ⟨metadata.coordinates, metadata.borrowBound, '+', '.join(balanced(chunks[name]) for name,_ in shapes)+'⟩\n')
    yield stem+'.Data',(f'import {stem}.Typed\nimport Airbender.Import.GKRProtocol.NumericHelperValidityImport\n\n'+header(case)+'\n'.join(lines)+end)
    lines=['attribute [local irreducible] original data\n',
        'numeric_data_binding coordinates_binding : data.coordinates = original.coordinates\n',
        'numeric_data_binding borrowBound_binding : data.borrowBound = original.borrowBound\n']
    for field,size in shapes:
        leaves=[]
        for first in range(0,size,4):
            width=min(4,size-first);chunk=field+str(first)
            lines.append(f'numeric_data_binding {chunk}_view : (data.{field}.drop {first}).take {width} = {chunk}.{field}\n')
            lines.append(f'numeric_data_binding {chunk}_piece : {chunk}.{field} = (original.{field}.drop {first}).take {width}\n')
            name=chunk+'_binding';lines.append(f'theorem {name} : (data.{field}.drop {first}).take {width} = (original.{field}.drop {first}).take {width} :=\n  {chunk}_view.trans {chunk}_piece\n');leaves.append((name,width))
        whole=merge(field,'data.'+field,'original.'+field,0,leaves,lines)
        lines.append(f'theorem {field}_binding : data.{field} = original.{field} :=\n  NumericQueryFrameChecks.complete_binding data.{field} original.{field} {size}\n    (by decide +kernel) (by decide +kernel) {whole}\n')
    lines.append('theorem source_binding : data = original :=\n  NumericHelperValidityChecks.capture_eq data original coordinates_binding borrowBound_binding\n    protectedFields_binding borrows_binding transports_binding\n')
    yield stem+'.Bindings',(f'import {stem}.Data\nimport Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n'+header(case)+'\n'.join(lines)+end)
    yield stem+'.Certificate',(f'import {stem}.Bindings\n\n'+header(case)+'theorem checked : NumericHelperValidityChecks.check babyBearModulus data = true := by decide +kernel\n\ndef facts :=\n  NumericHelperValidityChecks.check_sound data '+source(case).removeprefix('NumericHelperValidityChecks.ofTyped ')+'\n    source_binding checked\n'+end)


def native(case):
    text=original(case);start=text.index('namespace Airbender.Compiler.HelperValidityNative.');text=text[start:]
    text=text.replace('set_option maxHeartbeats 4000000\n','')
    pos=text.index('\n\ntheorem helper_graph_extends')
    text=text[:pos].rstrip()+' phase 1 using_checks Airbender.Compiler.HelperValidityChecks.'+case+text[pos:]
    return 'Airbender.Proofs.GKRProtocol.HelperValidityNative.'+case, f'import Airbender.Proofs.GKRProtocol.HelperValidityChecks.{case}.Certificate\n\n'+text


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case',choices=CASES,action='append')
    for flag in ['write','check']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args();generated=[entry for case in args.case or CASES for entry in [*modules(case),native(case)]]
    if args.write:preflight({LEAN/(module.replace('.','/')+'.lean'):text for module,text in generated})
    for module,text in generated:
        path=LEAN/(module.replace('.','/')+'.lean')
        if args.write:path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
        if args.check and (not path.exists() or path.read_text()!=text):raise SystemExit('stale helper capture: '+str(path))
    print('PASS complete helper captures:',len(args.case or CASES))


if __name__=='__main__':main()
