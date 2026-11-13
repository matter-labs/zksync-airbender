#!/usr/bin/env python3
"""Emit complete native sparse gate and placement bindings. The kernel checks every equality."""
from pathlib import Path
import json,sys
root=Path(__file__).resolve().parents[1]
families={'AddSub':'add-sub','Bigint':'bigint','BlakeG':'blake-g','BlakeRound':'blake-round','JumpBranch':'jump-branch','Keccak':'keccak','MulDiv':'mul-div','ShiftBinop':'shift-binop','SubwordMemory':'subword-memory','Unified':'unified','WordMemory':'word-memory'}
base={'LinearBaseFieldRelation','MaxQuadratic','EnforceSingleMaxQuadraticConstraint','CopyInBaseField','MaterializeSingleLookupInput'}
for family in sys.argv[1:] or families:
 c=json.load((root/f'artifacts/compiler/{families[family]}-cached.json').open())['circuit']
 ns=f'Airbender.Compiler.NativeBindings.{family}'
 native=f'Airbender.Compiler.FullArithmeticNative.{family}Cached.native'
 clean=f'Airbender.Compiler.CleanArithmeticNative.{family}Cached.native'
 capture=f'Airbender.Compiler.Captures.{family}.imported.circuit'
 directory=root/f'proven/Proven/Compiler/NativeBindings/{family}'
 directory.mkdir(parents=True,exist_ok=True)
 header=f'''module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.{family}
public import Proven.GKRProtocol.CleanArithmeticNative.{family}Cached

@[expose] public section
set_option warningAsError true
namespace {ns}
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768
'''
 clauses=[]
 for li,l in enumerate(c['layers']):
  for ci,(output,rel) in enumerate(l['cached_relations']):
   if 'SingleColumnLookup' in rel: clauses.append(('cache',li,ci))
 for li,l in enumerate(c['layers']):
  for gi,g in enumerate(l['gates']+l['gates_with_external_connections']):
   if next(iter(g['enforced_relation'])) in base: clauses.append(('gate',li,gi))
 imports=[];batches=[]
 for first in range(0,len(clauses),16):
  name=f'Gates{first//16:03d}';imports.append(f'Proven.Compiler.NativeBindings.{family}.{name}')
  s=header
  for i in range(first,min(first+16,len(clauses))):
   kind,li,idx=clauses[i]
   layer=f'({capture}).layers[{li}]\'(by decide)'
   if kind=='cache':
    entry=f'({layer}).cached_relations[{idx}]\'(by decide)'
    clause=f'(Clause.cache ({entry}).1 ({entry}).2)'
   else:
    entry=f'(({layer}).gates ++ ({layer}).gates_with_external_connections)[{idx}]\'(by decide)'
    clause=f'(Clause.gate ({entry}).enforced_relation)'
   s+=f'''\n/-- The actual native sparse relation supplies gate {i}. -/
theorem gate{i} (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds {capture} physical) :
    {native}.gate{i}.expressionResidual (physical ∘ {native}.bank.address) = 0 := by
  have checked : {native}.gate{i}.check = true :=
    List.all_eq_true.mp {native}.gatesChecked _ (List.get_mem _ ⟨{i}, by decide⟩)
  have binding : sparseResidual {native}.gate{i} (physical ∘ {native}.bank.address) =
      {clause}.residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans ({kind}_at accepted ⟨{li}, by decide⟩ ⟨{idx}, by decide⟩))
'''
  gates=', '.join(f'{native}.gate{i}' for i in range(first,min(first+16,len(clauses))))
  batch=f'gates{first//16:03d}';batches.append(batch)
  proof='(by intro gate member; cases member)'
  for i in reversed(range(first,min(first+16,len(clauses)))): proof=f'(cons_holds (gate{i} physical accepted) {proof})'
  s+=f'''\n/-- This batch retains every native scalar equation at these positions. -/
theorem {batch} (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds {capture} physical) :
    ∀ gate ∈ [{gates}], gate.expressionResidual (physical ∘ {native}.bank.address) = 0 :=
  {proof}
end {ns}
'''
  (directory/f'{name}.lean').write_text(s)
 # Each public placement is checked at its imported array position.
 count=len(c['placement_data'])
 placement_batches=[]
 placement_step=8 if family=="BlakeRound" else 24
 for first in range(0,count,placement_step):
  name=f'Placement{first//placement_step:03d}';imports.append(f'Proven.Compiler.NativeBindings.{family}.{name}')
  s=header
  for i in range(first,min(first+placement_step,count)):
   s+=f'''\n/-- Logical column {i} uses its actual native placement. -/
theorem placement{i} (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement {capture} physical logical) :
    ({clean}.environment physical (Verification.environment logical).data).get {i} = logical {i} := by
  have included := Array.getElem_mem (xs := ({capture}).placement_data.entries) (i := {i}) (by decide)
  have binding : ({capture}).placement_data.entries[{i}]\'(by decide) =
      ({i}, {native}.bank.address ({clean}.placement {i})) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))
'''
  batch=f'placements{first//placement_step:03d}';placement_batches.append(batch)
  proof='(by intro index member; cases member)'
  for i in reversed(range(first,min(first+placement_step,count))):proof=f'(cons_placements (placement{i} physical logical agreement) {proof})'
  s+=f'''\n/-- Public placements cover each column in this batch. -/
theorem {batch} (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement {capture} physical logical) :
    ∀ index ∈ {list(range(first,min(first+placement_step,count)))},
      ({clean}.environment physical (Verification.environment logical).data).get index = logical index :=
  {proof}
end {ns}
'''
  (directory/f'{name}.lean').write_text(s)
 # Separate complete composition.
 s='module\n'+''.join(f'public import {imp}\n' for imp in imports)+f'\n@[expose] public section\nset_option warningAsError true\nnamespace {ns}\nopen Airbender Airbender.Compiler NativeBridge\nset_option maxRecDepth 32768\n'
 proof='(by intro gate member; cases member)'
 for batch in reversed(batches):proof=f'(append_holds ({batch} physical accepted) {proof})'
 s+=f'''\n/-- Native acceptance supplies the complete checked arithmetic gate list. -/
theorem scalar_gates (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds {capture} physical) :
    ∀ gate ∈ {native}.artifact.gates,
      gate.expressionResidual (physical ∘ {native}.bank.address) = 0 :=
  {proof}
'''
 # Concrete finite cases avoid a large find operation in the proof.
 terms=', '.join(f'placements{i:03d} physical logical agreement' for i in range(len(placement_batches)))
 # Generic append placement function is added to NativeBridge.
 proof='(by intro index member; cases member)'
 for batch in reversed(placement_batches):proof=f'(append_placements ({batch} physical logical agreement) {proof})'
 s+=f'''\n/-- Public placement agreement supplies all variables used by the description. -/
theorem environment (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement {capture} physical logical) :
    ∀ index < {count},
      ({clean}.environment physical (Verification.environment logical).data).get index = logical index := by
  have all : ∀ index ∈ List.range {count},
      ({clean}.environment physical (Verification.environment logical).data).get index = logical index :=
    {proof}
  intro index bound
  exact all index (List.mem_range.mpr bound)

/-- The checked Clean expressions are the actual imported structured statements. -/
theorem equations : {clean}.expressions.map FlatOperation.assert = Circuit.equations {capture} := by
  kernel_rfl

/-- Native cached arithmetic preserves the public constraint description. -/
theorem arithmetic : {family}CachedArithmeticClaim := by
  intro physical logical accepted agreement
  rw [← equations]
  exact assertions_transport {clean}.expressions _ _ {count} {clean}.scopeChecked
    (environment physical logical agreement)
    ({clean}.arithmetic_preserved physical (Verification.environment logical).data (scalar_gates physical accepted))
end {ns}
'''
 (directory.parent/f'{family}.lean').write_text(s)
 print(family,'scalar gates',len(clauses),'placements',count,'modules',len(imports)+1)
