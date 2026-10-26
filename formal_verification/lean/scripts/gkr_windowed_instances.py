#!/usr/bin/env python3
"""Instantiate full native graph evaluation with actual per-set initialization top bits."""
from pathlib import Path
import argparse
import json
import os
import subprocess

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--mode',choices=['uncached','cached'],action='append')
for flag in ['write','check','build']:parser.add_argument('--'+flag,action='store_true')
args=parser.parse_args()
from gkr_functional_instances import selectors,PRODUCT
for mode in args.mode or ['uncached','cached']:
 case='Unified'+mode.title();pair=json.load(open('artifacts/compiler/unified-'+mode+'.json'));selection=selectors(pair['circuit'])
 chosen=[];product=0
 for layer in pair['circuit']['layers']:
  for gate in layer['gates']+layer['gates_with_external_connections']:
   kind,data=next(iter(gate['enforced_relation'].items()))
   if kind in PRODUCT:
    if kind=='InitsOrTeardownsInitialPair':chosen.append((selection['product_steps'][product],product))
    product+=1
 ns='Airbender.Compiler.WindowedNative.'+case
 text=(f'import Airbender.Import.GKRProtocol.InitializationWindowImport\nimport Airbender.Proofs.GKRProtocol.FunctionalNative.{case}\n\nnamespace {ns}\nopen Airbender Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
       f'import_initialization_windows native from "artifacts/compiler/unified-{mode}.json"\n\n')
 old=f'Airbender.Compiler.FunctionalNative.{case}.native'
 replacements={step:i for i,(step,_) in enumerate(chosen)}
 for step,i in replacements.items():
  text+=f'theorem shape{i} (publicTops : Nat → Nat) :\n    (nativeGate{i} publicTops).functional.outputs = {old}.step{step}.outputs ∧\n    (nativeGate{i} publicTops).functional.inputs = {old}.step{step}.inputs := by exact ⟨rfl, rfl⟩\n\n'
 for i,(step,product_index) in enumerate(chosen):
  text+=f'theorem specialization{i} : nativeGate{i} id = Airbender.Compiler.ProductNative.{case}.native.gate{product_index} := by rfl\n\n'
 text+='noncomputable def program (publicTops : Nat → Nat) : FunctionalProgram :=\n  ['+', '.join(f'(nativeGate{replacements[i]} publicTops).functional' if i in replacements else f'{old}.step{i}' for i in range(selection['steps']))+']\n\n'
 checks='List.Forall₂.nil'
 for i in reversed(range(selection['steps'])):
  same=f'shape{replacements[i]} publicTops' if i in replacements else '⟨rfl, rfl⟩'
  checks=f'List.Forall₂.cons ({same}) ({checks})'
 text+=(f'theorem program_shape (publicTops : Nat → Nat) :\n    List.Forall₂ (fun first second => second.outputs = first.outputs ∧ second.inputs = first.inputs) {old}.program (program publicTops) := by\n  exact {checks}\n\n'
        f'theorem valid (publicTops : Nat → Nat) : (program publicTops).Valid {old}.isBase [] :=\n  {old}.valid.replace (program_shape publicTops)\n\n'
        f'noncomputable def canonical {{R : Type}} [CommRing R] (publicTops : Nat → Nat)\n    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R) (physical : GKRAddress → Source.BaseField) : GKRAddress → R :=\n  Functional.read {old}.isBase (hom ∘ physical)\n    ((program publicTops).execute hom challenges gamma {old}.isBase (hom ∘ physical) (fun _ => 0))\n\n'
        f'theorem canonical_steps {{R : Type}} [CommRing R] (publicTops : Nat → Nat)\n    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R) (physical : GKRAddress → Source.BaseField) :\n    ∀ step ∈ program publicTops, step.Holds hom challenges gamma (canonical publicTops hom challenges gamma physical) :=\n  (FunctionalProgram.execute_sound (valid publicTops) hom challenges gamma (hom ∘ physical) (fun _ => 0)).1\n\nend {ns}\n')
 path=Path('Airbender/Proofs/GKRProtocol/WindowedNative')/(case+'Foundation.lean')
 if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('windowed foundation changed: '+case)
 if args.write:path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
 print('Airbender.Proofs.GKRProtocol.WindowedNative.'+case+'Foundation',flush=True)
 if args.build:subprocess.run(['lake','--no-cache','build','+Airbender.Proofs.GKRProtocol.WindowedNative.'+case+'Foundation:olean'],env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)


 text=(f'import Airbender.Proofs.GKRProtocol.WindowedNative.{case}Foundation\nimport Airbender.Proofs.GKRProtocol.BaseAffine\n\nnamespace {ns}\nopen Airbender Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n')
 common=('    {R : Type} [CommRing R] (publicTops : Nat → Nat)\n'
         '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)\n'
         '    (physical : GKRAddress → Source.BaseField)')
 value='(canonical publicTops hom challenges gamma physical)'
 for i in range(selection['steps']):
  step=f'(nativeGate{replacements[i]} publicTops).functional' if i in replacements else f'{old}.step{i}'
  membership='List.mem_cons_self'
  for _ in range(i):membership=f'List.mem_cons_of_mem _ ({membership})'
  text+=f'theorem stepHolds{i}\n'+common+f' :\n    ({step}).Holds hom challenges gamma {value} :=\n  canonical_steps publicTops hom challenges gamma physical ({step}) ({membership})\n\n'
 text+='theorem canonical_base\n'+common+f' (address : GKRAddress) (role : {old}.isBase address = true) :\n    canonical publicTops hom challenges gamma physical address = hom (physical address) := by\n  change (if {old}.isBase address then _ else _) = _\n  exact if_pos role\n\n'
 for i,step in enumerate(selection['lookup_steps']):
  text+=f'theorem lookupHolds{i}\n'+common+f' :\n    Airbender.Compiler.LookupNative.{case}.native.gate{i}.Holds hom challenges gamma {value} :=\n  Airbender.Compiler.LookupNative.{case}.native.gate{i}.functional_sound hom challenges gamma {value} (stepHolds{step} publicTops hom challenges gamma physical)\n\n'
 newproducts=[]
 for i,step in enumerate(selection['product_steps']):
  gate=f'(nativeGate{replacements[step]} publicTops)' if step in replacements else f'Airbender.Compiler.ProductNative.{case}.native.gate{i}'
  newproducts.append(gate)
  if step in selection['lookup_steps']:
   proof=f'by exact (stepHolds{step} publicTops hom challenges gamma physical) _ List.mem_cons_self'
  else:proof=f'{gate}.functional_sound hom challenges gamma {value} (stepHolds{step} publicTops hom challenges gamma physical)'
  text+=f'theorem productHolds{i}\n'+common+f' :\n    {gate}.Holds hom challenges {value} :=\n  {proof}\n\n'
 text+='noncomputable def productGates (publicTops : Nat → Nat) : List NativeProductGate := ['+', '.join(newproducts)+']\n\n'
 for kind,inventory,count in [('lookup',f'Airbender.Compiler.LookupNative.{case}.native.gates',len(selection['lookup_steps'])),('product','productGates publicTops',len(newproducts))]:
  checks='PredicateChecks.nil'
  for i in reversed(range(count)):checks=f'PredicateChecks.cons ({kind}Holds{i} publicTops hom challenges gamma physical) ({checks})'
  extra=' gamma' if kind=='lookup' else ''
  text+=f'theorem canonical_{kind}s\n'+common+f' :\n    ∀ gate ∈ {inventory}, gate.Holds hom challenges{extra} {value} :=\n  PredicateChecks.all ({checks})\n\n'
 base=f'Airbender.Compiler.FullArithmeticNative.{case}.native'
 arithmetic=f'    (arithmetic : ∀ gate ∈ {base}.artifact.gates, gate.expressionResidual (physical ∘ {base}.bank.address) = 0)'
 for i,step in enumerate(selection['affine_steps']):
  if step is not None:
   proof=(f'by\n    have bridge (values : GKRAddress → R) (equation : {old}.step{step}.Holds hom challenges gamma values) : {old}.affine{i}.Holds hom challenges values := by\n      exact equation (({old}.step{step}).get ⟨0, by decide +kernel⟩) (List.get_mem {old}.step{step} ⟨0, by decide +kernel⟩)\n    exact bridge {value} (stepHolds{step} publicTops hom challenges gamma physical)')
  else:
   ordinal=next(j for j,b in enumerate(selection['base']) if b['affine']==i);gate=selection['base'][ordinal]['gate']
   proof=(f'NativeBaseRecipe.definition_of_gate {old}.baseRecipe{ordinal} {base}.bank {old}.isBase {old}.baseOutput{ordinal} {base}.gate{gate} {old}.basePortsChecked{ordinal} {old}.baseRelationChecked{ordinal} {base}.gateChecked{gate} hom challenges physical {value} (canonical_base publicTops hom challenges gamma physical) (arithmetic _ (List.get_mem {base}.artifact.gates ⟨{gate}, by decide +kernel⟩))')
  affine_argument=arithmetic if step is None else arithmetic.replace('(arithmetic :','(_arithmetic :')
  text+=f'theorem affineHolds{i}\n'+common+'\n'+affine_argument+f' :\n    {old}.affine{i}.Holds hom challenges {value} :=\n  {proof}\n\n'
 checks='PredicateChecks.nil'
 for i in reversed(range(len(selection['affine_steps']))):checks=f'PredicateChecks.cons (affineHolds{i} publicTops hom challenges gamma physical arithmetic) ({checks})'
 text+='theorem canonical_affines\n'+common+'\n'+arithmetic+f' :\n    ∀ definition ∈ {old}.definitions, definition.Holds hom challenges {value} :=\n  PredicateChecks.all ({checks})\n\nend {ns}\n'
 path=Path('Airbender/Proofs/GKRProtocol/WindowedNative')/(case+'.lean')
 if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('windowed graph changed: '+case)
 if args.write:path.write_text(text)
 print('Airbender.Proofs.GKRProtocol.WindowedNative.'+case,flush=True)
 if args.build:subprocess.run(['lake','--no-cache','build','+Airbender.Proofs.GKRProtocol.WindowedNative.'+case+':olean'],env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)
