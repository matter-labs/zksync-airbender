#!/usr/bin/env python3
"""Preserve unified initialization products and bind explicit public address inputs."""
import argparse
import os
import subprocess
from export_gkr_translations import LEAN


def module(mode):
    case='Unified'+mode.title()
    ns='Airbender.Compiler.InitializationPortsNative.'+case
    memory=f'Airbender.Compiler.MemoryNative.{case}.native'
    text=(f'import Airbender.Proofs.GKRProtocol.InitializationPublic\nimport Airbender.Proofs.GKRProtocol.MemoryNative.{case}\n'
          f'import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.{case}\nimport Airbender.Proofs.GKRProtocol.NativeWitness\n'
          'import Airbender.Review.Circuits.Initialization.Artifact\n\n'
          f'namespace {ns}\nopen Airbender Airbender.Compiler\n'
          'set_option warningAsError true\nset_option Elab.async false\n'
          'set_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n')
    text+=('theorem geometry : Initialization.unified.layout.rows = 8388608 ∧\n'
           '    Initialization.unified.layout.stride = 512 ∧ Initialization.unified.layout.columns.size = 2 := by decide +kernel\n\n')
    for direction,stage in [('read','terminal'),('write','initial')]:
        rows=memory+'.initialization'+direction.title()+'Rows'
        text+=(f'theorem source_{direction}_tokens (physical : GKRAddress → Source.BaseField) :\n'
               f'    {rows}.map (fun row => row.token ({memory}.sourceValues physical)) =\n'
               f'      (List.finRange 2).map (fun set => sourceBoundaryToken ({memory}.sourceValues physical) .{stage} set.val 512) := by rfl\n\n')
        text+=(f'theorem {direction}_products_from_base {{R : Type}} [CommRing R]\n'
               '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)\n'
               '    (physical : GKRAddress → Source.BaseField) :\n'
               f'    ({rows}.map (fun row => row.fingerprint ({memory}.sourceValues physical) hom challenges)).prod =\n'
               f'      (((List.finRange 2).map (fun set => sourceBoundaryToken ({memory}.sourceValues physical) .{stage} set.val 512)).map\n'
               '        (memoryTokenFingerprint hom challenges)).prod := by\n'
               f'  rw [← Source.MemoryRow.token_products {rows} ({memory}.sourceValues physical) hom challenges, source_{direction}_tokens physical]\n\n')
    text+=(f'theorem raw_columns (physical : GKRAddress → Source.BaseField)\n'
           f'    (set : Fin Initialization.unified.layout.columns.size) :\n'
           f'    ({memory}.sourceValues physical).teardownTimestamp set.val 0 = physical (.BaseLayerMemory Initialization.unified.layout.columns[set].timeLo) ∧\n'
           f'    ({memory}.sourceValues physical).teardownTimestamp set.val 1 = physical (.BaseLayerMemory Initialization.unified.layout.columns[set].timeHi) ∧\n'
           f'    ({memory}.sourceValues physical).teardownValue set.val 0 = physical (.BaseLayerMemory Initialization.unified.layout.columns[set].valueLo) ∧\n'
           f'    ({memory}.sourceValues physical).teardownValue set.val 1 = physical (.BaseLayerMemory Initialization.unified.layout.columns[set].valueHi) := by\n'
           '  fin_cases set <;> exact ⟨rfl, rfl, rfl, rfl⟩\n\n')
    text+=(f'theorem public_leaf (physical : GKRAddress → Source.BaseField)\n'
           '    (parameters : Initialization.Parameters babyBearModulus Source.BaseField)\n'
           '    (row : Fin 8388608) (window : Nat) (windowBound : window + 1 < 128)\n'
           '    (windows : ∀ set : Fin 2, parameters.windows set.val = window + set.val)\n'
           f'    (low : ({memory}.sourceValues physical).initializationAddress 0 = (Initialization.addressLo row.val : Source.BaseField))\n'
           f'    (high : ({memory}.sourceValues physical).initializationAddress 1 = (row.val / 16384 + window * 512 : Nat))\n'
           '    (stageKind : Initialization.Phase) (set : Fin 2) :\n'
           f'    sourceBoundaryToken ({memory}.sourceValues physical) stageKind set.val 512 =\n'
           '      (Initialization.Leaf.mk stageKind set.val Initialization.unified.layout.columns[set]).token\n'
           '        Initialization.unified.layout parameters (fun _ column => physical (.BaseLayerMemory column)) row.val := by\n'
           f'  have addresses := inline_public_addresses parameters ({memory}.sourceValues physical) row window windows low high set\n'
           '  have bounds := inline_public_bounds parameters row window windowBound windows set\n'
           '  have raw := raw_columns physical set\n'
           f'  exact source_boundary_leaf Initialization.unified.layout parameters ({memory}.sourceValues physical)\n'
           '    (fun _ column => physical (.BaseLayerMemory column)) stageKind set row addresses.1 addresses.2 bounds.1 bounds.2\n'
           '      raw.1 raw.2.1 raw.2.2.1 raw.2.2.2\n\n')
    executor=(LEAN/'Airbender/Proofs/GKRProtocol/MemoryPortsNative/UnifiedUncached.lean').read_text().replace('UnifiedUncached',case)
    for direction,stage in [('read','terminal'),('write','initial')]:
        first=executor.index('theorem '+direction+'_output_logical')
        last=executor.find('theorem write_output_logical',first+1) if direction=='read' else executor.index('\nend Airbender.Compiler.MemoryPortsNative.')
        block=executor[first:last]
        body=block[block.index('  let assignment'):block.index('  change values')]
        body=body.replace('.memory'+direction.title()+'SourceReduction','.initialization'+direction.title()+'SourceReduction')
        text+=(f'theorem {direction}_output_tokens {{R : Type}} [CommRing R]\n'
               '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)\n'
               '    (physical : GKRAddress → Source.BaseField) (values : GKRAddress → R)\n'
               f'    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.{case}.native.isBase address = true → values address = hom (physical address))\n'
               f'    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.{case}.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.{case}.native.bank.address) = 0)\n'
               f'    (affine : ∀ definition ∈ Airbender.Compiler.FunctionalNative.{case}.native.definitions, definition.Holds hom challenges values)\n'
               f'    (products : ∀ gate ∈ Airbender.Compiler.ProductNative.{case}.native.gates, gate.Holds hom challenges values) :\n'
               f'    values {memory}.initialization{direction.title()}Output =\n'
               f'      (((List.finRange 2).map (fun set => sourceBoundaryToken ({memory}.sourceValues physical) .{stage} set.val 512)).map\n'
               '        (memoryTokenFingerprint hom challenges)).prod := by\n'+body+
               f'  change values {memory}.initialization{direction.title()}Output =\n'
               f'    ({memory}.initialization{direction.title()}Rows.map (fun row => row.fingerprint ({memory}.sourceValues physical) hom challenges)).prod at reduced\n'
               f'  rw [{direction}_products_from_base hom challenges physical] at reduced\n  exact reduced\n\n')
    for direction,stage in [('read','terminal'),('write','initial')]:
        text+=(f'theorem {direction}_output_public {{R : Type}} [CommRing R]\n'
               '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)\n'
               '    (physical : GKRAddress → Source.BaseField) (values : GKRAddress → R)\n'
               '    (parameters : Initialization.Parameters babyBearModulus Source.BaseField)\n'
               '    (row : Fin 8388608) (window : Nat) (windowBound : window + 1 < 128)\n'
               '    (windows : ∀ set : Fin 2, parameters.windows set.val = window + set.val)\n'
               f'    (low : ({memory}.sourceValues physical).initializationAddress 0 = (Initialization.addressLo row.val : Source.BaseField))\n'
               f'    (high : ({memory}.sourceValues physical).initializationAddress 1 = (row.val / 16384 + window * 512 : Nat))\n'
               f'    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.{case}.native.isBase address = true → values address = hom (physical address))\n'
               f'    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.{case}.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.{case}.native.bank.address) = 0)\n'
               f'    (affine : ∀ definition ∈ Airbender.Compiler.FunctionalNative.{case}.native.definitions, definition.Holds hom challenges values)\n'
               f'    (products : ∀ gate ∈ Airbender.Compiler.ProductNative.{case}.native.gates, gate.Holds hom challenges values) :\n'
               f'    values {memory}.initialization{direction.title()}Output =\n'
               f'      ((Initialization.unified.layout.leaves .{stage}).map (fun leaf =>\n'
               '        memoryTokenFingerprint hom challenges (leaf.token Initialization.unified.layout parameters\n'
               '          (fun _ column => physical (.BaseLayerMemory column)) row.val))).prod := by\n'
               f'  rw [{direction}_output_tokens hom challenges physical values baseLaw arithmetic affine products]\n'
               f'  have identity : (List.finRange 2).map (fun set => sourceBoundaryToken ({memory}.sourceValues physical) .{stage} set.val 512) =\n'
               f'      (Initialization.unified.layout.leaves .{stage}).map (fun leaf => leaf.token Initialization.unified.layout parameters\n'
               '        (fun _ column => physical (.BaseLayerMemory column)) row.val) := by\n'
               '    simp only [Initialization.Layout.leaves, List.map_map]\n'
               '    change _ = (List.finRange 2).map _\n'
               '    apply List.map_congr_left\n    intro set member\n'
               f'    exact public_leaf physical parameters row window windowBound windows low high .{stage} set\n'
               '  rw [identity]\n  simp only [List.map_map, Function.comp_def]\n\n')
    text+=f'end {ns}\n'
    return 'Airbender.Proofs.GKRProtocol.InitializationPortsNative.'+case,text


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--mode',choices=['cached','uncached'],action='append')
    for flag in ['write','check','build']:p.add_argument('--'+flag,action='store_true')
    a=p.parse_args()
    for mode in a.mode or ['uncached','cached']:
        target,text=module(mode);path=LEAN/(target.replace('.','/')+'.lean')
        if a.check and (not path.exists() or path.read_text()!=text):raise ValueError('initialization token bridge changed: '+target)
        if a.write:path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
        print(target,flush=True)
        if a.build:subprocess.run(['lake','--no-cache','build','+'+target+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)


if __name__=='__main__':main()
