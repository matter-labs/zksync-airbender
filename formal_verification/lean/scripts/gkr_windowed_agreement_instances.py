#!/usr/bin/env python3
"""Check that actual public-window changes leave unrelated graph outputs equal."""
import argparse
import json
import os
import subprocess
from export_gkr_translations import LEAN
from gkr_functional_instances import selectors,BASE,PRODUCT


def key(a):return json.dumps(a,sort_keys=True)

def address(a):
    kind,value=next(iter(a.items()))
    if kind in ['BaseLayerWitness','BaseLayerMemory','Setup','ScratchSpace']:return f'(GKRAddress.{kind} {value})'
    if kind in ['InnerLayer','Cached']:return f'(GKRAddress.{kind} {value["layer"]} {value["offset"]})'
    if kind=='VirtualSetup':return f'(GKRAddress.VirtualSetup .{value})'
    raise ValueError(a)


def contained(x):
    if isinstance(x,dict):
        if len(x)==1 and next(iter(x)) in ['BaseLayerWitness','BaseLayerMemory','Setup','ScratchSpace','InnerLayer','Cached','VirtualSetup']:
            return [x]
        return sum((contained(v) for v in x.values()),[])
    if isinstance(x,list):return sum((contained(v) for v in x),[])
    return []


def module(mode):
    case='Unified'+mode.title();old=f'Airbender.Compiler.FunctionalNative.{case}.native'
    pair=json.loads((LEAN/'artifacts/compiler'/('unified-'+mode+'.json')).read_text());c=pair['circuit'];sel=selectors(c)
    gates=[next(iter(g['enforced_relation'].items())) for layer in c['layers'] for g in layer['gates']+layer['gates_with_external_connections']]
    caches=[(out,rel) for layer in c['layers'] for out,rel in layer['cached_relations']]
    # Reproduce only candidate dependencies. Every actual step input is checked
    # against the accumulated equalities by the kernel below.
    records=[];idx=0
    for out,rel in caches:
        if 'SingleColumnLookup' not in rel:records.append((idx,[out],contained(rel),False));idx+=1
    pidx=0
    for kind,data in gates:
        lookup=kind.startswith('Lookup') or kind in ['AggregateLookupRationalPair','CopyInExtensionField']
        product=kind in PRODUCT
        out=data.get('output') if isinstance(data,dict) else None
        outs=out if isinstance(out,list) else [out] if out else []
        deps=contained({k:v for k,v in data.items() if k!='output'}) if isinstance(data,dict) else contained(data)
        changed=kind=='InitsOrTeardownsInitialPair'
        if lookup:records.append((idx,outs,deps,changed));idx+=1
        if product:
            if not lookup:records.append((idx,outs,deps,changed));idx+=1
            pidx+=1
        if kind=='MaterializedVectorLookupInput':records.append((idx,outs,deps,False));idx+=1
    assert idx==sel['steps']
    text=(f'import Airbender.Proofs.GKRProtocol.WindowedNative.{case}\nimport Airbender.Proofs.GKRProtocol.FunctionalAgreement\n\n'
          f'namespace Airbender.Compiler.WindowedNative.{case}\nopen Airbender Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n')
    common=('    {R : Type} [CommRing R] (publicTops : Nat → Nat)\n'
            '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)\n'
            '    (physical : GKRAddress → Source.BaseField)')
    left='canonical publicTops hom challenges gamma physical';right=f'{old}.canonical hom challenges gamma physical'
    known={};known_addresses={};affected=set()
    # Base candidates are obtained from all actual JSON addresses and memory
    # layout. Redundant candidates are harmless; each claimed base role is checked.
    base={key(a):a for a in contained(c) if next(iter(a)) in ['BaseLayerWitness','BaseLayerMemory','Setup','VirtualSetup']}
    for out,rel in caches:
        if 'SingleColumnLookup' in rel:base[key(out)]=out
    for kind,data in gates:
        if kind in BASE and 'output' in data:
            out=data['output'];base[key(out)]=out
    for n,a in enumerate(base.values()):
        term=address(a);name='baseAgree'+str(n);known[key(a)]=name;known_addresses[key(a)]=a
        text+=f'theorem {name}\n'+common+f' :\n    {left} {term} = {right} {term} := by\n  rw [canonical_base publicTops hom challenges gamma physical {term} (by decide +kernel), {old}.canonical_base hom challenges gamma physical {term} (by decide +kernel)]\n\n'
    for step,outs,deps,changed in records:
        if changed or any(key(a) in affected for a in deps):
            affected.update(key(a) for a in outs);continue
        # Keep only already established candidates; exact actual-input coverage
        # is checked in the generated list-membership proof.
        candidates=dict(known_addresses)
        proofs=[]
        for a in candidates.values():proofs.append(f'{known[key(a)]} publicTops hom challenges gamma physical')
        list_terms=', '.join(address(a) for a in candidates.values())
        checks='PredicateChecks.nil'
        for proof in reversed(proofs):checks=f'PredicateChecks.cons ({proof}) ({checks})'
        input_name=f'inputsAgree{step}'
        text+=f'theorem {input_name}\n'+common+f' :\n    ∀ entry ∈ {old}.step{step}.inputs, {left} entry = {right} entry := by\n'
        text+=f'  have available : ∀ entry ∈ ([{list_terms}] : List GKRAddress), {left} entry = {right} entry := PredicateChecks.all ({checks})\n'
        text+=f'  intro entry member\n  apply available\n  have coverage : {old}.step{step}.inputs.all (fun input => ([{list_terms}] : List GKRAddress).contains input) = true := by decide +kernel\n'
        text+='  exact List.mem_of_elem_eq_true (List.all_eq_true.mp coverage entry member)\n\n'
        for n,a in enumerate(outs):
            name=f'outputAgree{step}_{n}';term=address(a)
            member='List.mem_cons_self'
            for _ in range(n):member=f'List.mem_cons_of_mem _ ({member})'
            text+=f'theorem {name}\n'+common+f' :\n    {left} {term} = {right} {term} :=\n  FunctionalStep.output_agrees {old}.step{step} hom challenges gamma _ _ (stepHolds{step} publicTops hom challenges gamma physical) ({old}.canonical_step_holds hom challenges gamma physical {old}.step{step} (List.get_mem {old}.program ⟨{step}, by decide +kernel⟩)) ({input_name} publicTops hom challenges gamma physical) {term} ({member})\n\n'
            known[key(a)]=name;known_addresses[key(a)]=a
    for group,ports in c['global_output_map'].items():
        if group=='InitsAndTeardownsProduct':continue
        for i,a in enumerate(ports):
            assert key(a) in known,(group,a)
            text+=f'theorem {group}_output{i}_unchanged\n'+common+f' :\n    {left} {address(a)} = {right} {address(a)} :=\n  {known[key(a)]} publicTops hom challenges gamma physical\n\n'
    text+=f'end Airbender.Compiler.WindowedNative.{case}\n'
    return 'Airbender.Proofs.GKRProtocol.WindowedNative.'+case+'Agreement',text


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--mode',choices=['uncached','cached'],action='append')
    for flag in ['write','check','build']:p.add_argument('--'+flag,action='store_true')
    a=p.parse_args()
    for mode in a.mode or ['uncached','cached']:
        target,text=module(mode);path=LEAN/(target.replace('.','/')+'.lean')
        if a.check and (not path.exists() or path.read_text()!=text):raise ValueError('windowed agreement changed: '+target)
        if a.write:path.write_text(text)
        print(target,flush=True)
        if a.build:subprocess.run(['lake','--no-cache','build','+'+target+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)


if __name__=='__main__':main()
