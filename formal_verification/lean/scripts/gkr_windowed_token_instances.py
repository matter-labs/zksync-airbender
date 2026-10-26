#!/usr/bin/env python3
"""Compose actual public-window initialization factors through native output copies."""
import argparse
import json
import os
from pathlib import Path
import subprocess
from export_gkr_translations import LEAN
from gkr_functional_instances import PRODUCT


def module(mode):
    case='Unified'+mode.title();ns='Airbender.Compiler.WindowedNative.'+case
    text=(LEAN/'scripts/templates/gkr_windowed_tokens.lean').read_text().replace('UnifiedUncached',case)
    text=text[:text.index('end '+ns)]
    pair=json.loads((LEAN/'artifacts/compiler'/('unified-'+mode+'.json')).read_text())
    gates=[]
    for layer in pair['circuit']['layers']:
        for gate in layer['gates']+layer['gates_with_external_connections']:
            kind,data=next(iter(gate['enforced_relation'].items()))
            if kind in PRODUCT:gates.append((kind,data))
    def key(address):return json.dumps(address,sort_keys=True)
    copies={key(data['output']):(i,data['input']) for i,(kind,data) in enumerate(gates) if kind=='CopyInExtensionField'}
    outputs=pair['circuit']['global_output_map']['InitsAndTeardownsProduct']
    def membership(index):
        proof='List.mem_cons_self'
        for _ in range(index):proof=f'List.mem_cons_of_mem _ ({proof})'
        return proof
    common=('    {R : Type} [CommRing R] (publicTops : Nat → Nat)\n'
            '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)\n'
            '    (physical : GKRAddress → Source.BaseField) (values : GKRAddress → R)\n'
            f'    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.{case}.native.isBase address = true → values address = hom (physical address))\n'
            '    (products : ∀ gate ∈ productGates publicTops, gate.Holds hom challenges values)')
    for direction,gateIndex,stage,out in [('read',1,'terminal',outputs[0]),('write',0,'initial',outputs[1])]:
        path=[];cursor=out
        while key(cursor) in copies:
            index,cursor=copies[key(cursor)];path.append(index)
        expected=gates[4+gateIndex][1]['output'];assert cursor==expected
        wire=out['InnerLayer']
        text+=f'theorem {direction}_output_tokens\n'+common+f' :\n    values (.InnerLayer {wire["layer"]} {wire["offset"]}) =\n      (((List.finRange 2).map (fun set => windowedBoundaryToken (Airbender.Compiler.MemoryNative.{case}.native.sourceValues physical) publicTops .{stage} set.val 512)).map (memoryTokenFingerprint hom challenges)).prod := by\n'
        for index in path:
            text+=f'  have copy{index} := products Airbender.Compiler.ProductNative.{case}.native.gate{index} ({membership(index)})\n'
            text+=f'  change values _ = values _ at copy{index}\n  rw [copy{index}]\n'
        text+=f'  exact gate{gateIndex}_tokens publicTops hom challenges physical values baseLaw (products (nativeGate{gateIndex} publicTops) ({membership(4+gateIndex)}))\n\n'
        text+=f'theorem canonical_{direction}_tokens {{R : Type}} [CommRing R] (publicTops : Nat → Nat)\n    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)\n    (physical : GKRAddress → Source.BaseField) :\n    canonical publicTops hom challenges gamma physical (.InnerLayer {wire["layer"]} {wire["offset"]}) =\n      (((List.finRange 2).map (fun set => windowedBoundaryToken (Airbender.Compiler.MemoryNative.{case}.native.sourceValues physical) publicTops .{stage} set.val 512)).map (memoryTokenFingerprint hom challenges)).prod :=\n  {direction}_output_tokens publicTops hom challenges physical _ (canonical_base publicTops hom challenges gamma physical) (canonical_products publicTops hom challenges gamma physical)\n\n'
    text+='end '+ns+'\n'
    return 'Airbender.Proofs.GKRProtocol.WindowedNative.'+case+'Tokens',text


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--mode',choices=['uncached','cached'],action='append')
    for flag in ['write','check','build']:p.add_argument('--'+flag,action='store_true')
    a=p.parse_args()
    for mode in a.mode or ['uncached','cached']:
        target,text=module(mode);path=LEAN/(target.replace('.','/')+'.lean')
        if a.check and (not path.exists() or path.read_text()!=text):raise ValueError('windowed token graph changed: '+target)
        if a.write:path.write_text(text)
        print(target,flush=True)
        if a.build:subprocess.run(['lake','--no-cache','build','+'+target+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)


if __name__=='__main__':main()
