#!/usr/bin/env python3
"""Compose actual window-parametric native graphs with source/Clean trace witnesses."""
import argparse
import os
import subprocess
from export_gkr_translations import LEAN


def module(mode):
    case='Unified'+mode.title()
    old='Airbender.Compiler.FunctionalNative.'+case+'.native'
    win='Airbender.Compiler.WindowedNative.'+case
    lookup='Airbender.Compiler.MaterializedWitnessNative.'+case
    frame='Airbender.Compiler.FramedWitnessNative.'+case
    framed=(LEAN/'Airbender/Proofs/GKRProtocol/FramedWitnessNative'/f'{case}.lean').read_text()
    material=(LEAN/'Airbender/Proofs/GKRProtocol/MaterializedWitnessNative'/f'{case}.lean').read_text()
    row=material[material.index('def RowWitness'):material.index('\ntheorem native_lookup_trace_extends')]
    row=row.replace('def RowWitness {R','def ActualRowWitness (publicTops : Nat → Nat) {R')
    row=row.replace(f'Airbender.Compiler.ProductNative.{case}.native.gates',f'{win}.productGates publicTops')
    graph=framed[framed.index('theorem framed_graph_extends'):framed.index('\ndef MemoryOutputsPreserved')]
    graph=graph.replace('theorem framed_graph_extends {R','theorem graph_extends (publicTops : Nat → Nat) {R')
    graph=graph.replace('RowWitness hom', 'ActualRowWitness publicTops hom')
    # Expose the canonical assignment used by this constructive extension.
    graph=graph.replace('      ∀ address, addressEqual','      values = '+win+'.canonical publicTops hom challenges gamma baseValue ∧\n      ∀ address, addressEqual',1)
    for method in ['canonical','canonical_base','canonical_affines','canonical_lookups','canonical_products']:
        graph=graph.replace(f'{old}.{method} hom',f'{win}.{method} publicTops hom')
    graph=graph.replace('refine ⟨baseValue, values, ?_, externalAgreement⟩','refine ⟨baseValue, values, ?_, rfl, externalAgreement⟩')
    text=(f'import Airbender.Proofs.GKRProtocol.WindowedNative.{case}Tokens\nimport Airbender.Proofs.GKRProtocol.WindowedNative.{case}Agreement\n'
          f'import Airbender.Proofs.GKRProtocol.CleanWitnessNative.{case}\n\nnamespace {win}\n'
          'open Airbender Airbender.Compiler\n'+f'open {lookup}\n'
          'set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'+row+'\n'+graph)
    boundary=(LEAN/'scripts/templates/gkr_windowed_witness_boundary.lean').read_text()
    replacements={'OLD':old,'MODEL':f'Airbender.Compiler.MaterializedNative.{case}.native.model',
      'MEMORY':f'Airbender.Compiler.MemoryNative.{case}.native','FRAME_MEMORY':f'Airbender.Compiler.MemoryFrameNative.{case}.native',
      'BASE':f'Airbender.Compiler.FullArithmeticNative.{case}.native','CONTRACT':f'Airbender.Compiler.SourceContractNative.{case}.native',
      'HELPER':f'Airbender.Compiler.HelperValidityNative.{case}.native','FRAME':frame}
    for key,value in replacements.items():boundary=boundary.replace('@'+key+'@',value)
    text+='\n'+boundary
    complete=framed[framed.index('theorem complete_trace_extends'):framed.index('\ntheorem memory_trace_products_preserved')]
    complete=complete.replace('      ∀ {R : Type}', '      ∀ (publicTops : Nat → Nat) {R : Type}')
    complete=complete.replace('CompleteRowWitness hom challenges gamma (sourceValue row) (counts row) row (fallback row) (baseValue row) (values row)',
       'CompleteActualRowWitness publicTops hom challenges gamma (sourceValue row) (counts row) row (fallback row) (baseValue row) (values row)')
    complete=complete[:complete.index('  have complete (row')]+'''  have complete (row : Fin DOMAIN) :
      ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,
      CompleteActualRowWitness publicTops hom challenges gamma (sourceValue row) (counts row) row (fallback row) baseValue values :=
    complete_row_extends publicTops hom challenges gamma
      (sourceValue row) (original row) (clockValid row) (primitives row) (counts row) row (fallback row)
  choose baseValue values correct using complete
  refine ⟨baseValue, values, correct, ?_⟩
  intro group
  have same : ((List.finRange DOMAIN).map (fun row => (outputPorts group).value (values row))) =
      ((List.finRange DOMAIN).map (fun row =>
        (((sourceRequests (sourceValue row) group).map (fun query => query.value hom challenges.lookupAlpha gamma)) ++
          [(MODEL.row (setupColumns group) row (counts row group)).value hom challenges.lookupAlpha gamma]).sum)) := by
    apply List.map_congr_left
    intro row _
    exact outputs_preserved_uniform hom challenges gamma (sourceValue row) (counts row) row (values row)
      (correct row).1.2.2.2.2.2.2.2.2.2 group
  rw [same]
  exact cancel group hom challenges.lookupAlpha gamma
'''
    model=f'Airbender.Compiler.MaterializedNative.{case}.native.model'
    complete=complete.replace('DOMAIN',model+'.imported.data.length').replace('MODEL',model)
    complete=complete.replace('  intro R _ hom challenges gamma', '  intro publicTops R _ hom challenges gamma')
    text+='\n'+complete
    # Clean proof only consumes the base-field clauses of the same new witness.
    clean=(LEAN/'Airbender/Proofs/GKRProtocol/CleanWitnessNative'/f'{case}.lean').read_text()
    clean=clean[clean.index('theorem complete_trace_clean_extends'):clean.index('\nend ')]
    clean=clean.replace('      ∀ {R : Type}', '      ∀ (publicTops : Nat → Nat) {R : Type}')
    clean=clean.replace('CompleteRowWitness hom challenges gamma (sourceValue row) (counts row) row (fallback row) (baseValue row) (values row)',
       'CompleteActualRowWitness publicTops hom challenges gamma (sourceValue row) (counts row) row (fallback row) (baseValue row) (values row)')
    clean=clean.replace(f'{frame}.complete_trace_extends sourceValue','complete_trace_extends sourceValue')
    clean=clean.replace('  intro R _ hom challenges gamma', '  intro publicTops R _ hom challenges gamma')
    clean=clean.replace('constructed hom challenges gamma', 'constructed publicTops hom challenges gamma')
    
    text+='\n'+clean+f'\nend {win}\n'
    return 'Airbender.Proofs.GKRProtocol.WindowedNative.'+case+'Witness',text


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--mode',choices=['uncached','cached'],action='append')
    for flag in ['write','check','build']:p.add_argument('--'+flag,action='store_true')
    a=p.parse_args()
    for mode in a.mode or ['uncached','cached']:
        target,text=module(mode);path=LEAN/(target.replace('.','/')+'.lean')
        if a.check and (not path.exists() or path.read_text()!=text):raise ValueError('windowed witness changed: '+target)
        if a.write:path.write_text(text)
        print(target,flush=True)
        if a.build:subprocess.run(['lake','--no-cache','build','+'+target+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)


if __name__=='__main__':main()
