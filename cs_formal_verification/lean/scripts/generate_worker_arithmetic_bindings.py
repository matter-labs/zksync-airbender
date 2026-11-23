#!/usr/bin/env python3
"""Emit small kernel checks for the complete cached worker arithmetic bindings."""
from pathlib import Path
import json
root=Path(__file__).resolve().parents[1]
items={'KeccakColumnParity':'keccak-column-parity','KeccakThetaRho':'keccak-theta-rho','KeccakChi5':'keccak-chi5'}
def address(a):
 k,d=next(iter(a.items()))
 if isinstance(d,int):return f'(.{k} {d})'
 if isinstance(d,dict):return f'(.{k} {d["layer"]} {d["offset"]})'
 raise ValueError(a)
for title,name in items.items():
 cert=json.load(open(root/f'artifacts/compiler/description-arithmetic/{name}-cached.json'));c=json.load(open(root.parent.parent/f'cs/compiled_circuits/{name.replace("-","_")}_layout_gkr.json'))
 ns=f'Airbender.Compiler.WorkerBindings.{title}';native=f'Airbender.Compiler.WorkerArithmetic.{title}.native';capture=f'Airbender.Compiler.Captures.{title}.imported.circuit';n=cert['counts']['source_variables'];m=len(cert['addresses'])
 directory=root/f'proven/Proven/Compiler/WorkerBindings/{title}';directory.mkdir(parents=True,exist_ok=True)
 header=f'''module
public import Proven.Compiler.WorkerArithmetic.{title}
public import Human.Compiler.Captures.{title}
public import Proven.Compiler.DescriptionBridge
public import Proven.Compiler.Reverse
public import Proven.KernelExact
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace {ns}
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option maxRecDepth 32768
'''
 literals=', '.join(map(address,cert['addresses']))
 data=header+f'''/-- The retained bank gives a physical address to each arithmetic coordinate. -/
def addresses : Vector GKRAddress {m} := #v[{literals}]

/-- Read the checked arithmetic source placement at a logical index. -/
def placed (physical : GKRAddress → F) (logical : Nat → F) (index : Nat) : F :=
  if bound : index < {n} then physical addresses[{native}.artifact.placement ⟨index, bound⟩]
  else logical index
end {ns}
'''
 (directory/'Data.lean').write_text(data)
 common=header.replace('public import Proven.Compiler.DescriptionBridge',f'public import Proven.Compiler.DescriptionBridge\npublic import Proven.Compiler.WorkerBindings.{title}.Data')
 imports=[];placementBatches=[]
 for first in range(0,n,16):
  namepart=f'Placement{first//16:03d}';imports.append(f'Proven.Compiler.WorkerBindings.{title}.{namepart}');text=common
  for i in range(first,min(n,first+16)):
   a=address(c['placement_data'][str(i)]);position=list(c['placement_data']).index(str(i))
   text+=f'''/-- This source column has its actual captured physical placement. -/
theorem placement{i} (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement {capture} physical logical) :
    placed physical logical {i} = logical {i} := by
  have member := Array.getElem_mem (xs := ({capture}).placement_data.entries)
    (i := {position}) (by decide)
  have entry : ({capture}).placement_data.entries[{position}]'(by decide) = ({i}, {a}) := by kernel_rfl
  rw [entry] at member
  exact (agreement _ member).symm
'''
  proof='(by intro index member; cases member)'
  for i in reversed(range(first,min(n,first+16))):proof=f'(cons_placements (placement{i} physical logical agreement) {proof})'
  batch=f'placements{first//16:03d}';placementBatches.append(batch)
  text+=f'''theorem {batch} (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement {capture} physical logical) :
    ∀ index ∈ List.range' {first} {min(16,n-first)}, placed physical logical index = logical index :=
  {proof}
end {ns}
''';(directory/f'{namepart}.lean').write_text(text)
 clauses=[]
 for li,layer in enumerate(c['layers']):
  for ci,(_,relation) in enumerate(layer['cached_relations']):
   if 'SingleColumnLookup' in relation:clauses.append(('cache',li,ci))
 for li,layer in enumerate(c['layers']):
  for gi,gate in enumerate(layer['gates']+layer['gates_with_external_connections']):
   if next(iter(gate['enforced_relation'])) in {'CopyInBaseField','MaxQuadratic','EnforceSingleMaxQuadraticConstraint','LinearBaseFieldRelation'}:clauses.append(('gate',li,gi))
 def clause_at(i):
  kind,li,position=clauses[i];layer=f'({capture}).layers[{li}]\'(by decide)'
  if kind=='cache':
   entry=f'({layer}).cached_relations[{position}]\'(by decide)'
   return f'(Clause.cache ({entry}).1 ({entry}).2)'
  entry=f'(({layer}).gates ++ ({layer}).gates_with_external_connections)[{position}]\'(by decide)'
  return f'(Clause.gate ({entry}).enforced_relation)'
 gateBatches=[];clauseBatches=[]
 for first in range(0,len(clauses),8):
  part=f'Gates{first//8:03d}';imports.append(f'Proven.Compiler.WorkerBindings.{title}.{part}');text=common
  for i in range(first,min(len(clauses),first+8)):
   kind,li,position=clauses[i];clause=clause_at(i)
   text+=f'''/-- This typed sparse residual is the actual physical native relation. -/
theorem binding{i} (physical : GKRAddress → F) :
    sparseResidual {native}.gate{i} (fun index => physical addresses[index]) =
      {clause}.residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate{i} (physical : GKRAddress → F) (accepted : Holds {capture} physical) :
    {native}.gate{i}.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : {native}.gate{i}.check = true :=
    List.all_eq_true.mp {native}.gatesChecked _ (List.get_mem _ ⟨{i}, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding{i} physical).trans ({kind}_at accepted ⟨{li}, by decide⟩ ⟨{position}, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause{i} (physical : GKRAddress → F)
    (holds : {native}.artifact.LoweredHolds (fun index => physical addresses[index])) :
    {clause}.residual physical = 0 := by
  have checked : {native}.gate{i}.check = true :=
    List.all_eq_true.mp {native}.gatesChecked _ (List.get_mem _ ⟨{i}, by decide⟩)
  exact (binding{i} physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨{i}, by decide⟩)))
'''
  proof='(by intro gate member; cases member)'
  reverse='(by intro clause member; cases member)'
  for i in reversed(range(first,min(len(clauses),first+8))):
   proof=f'(cons_holds (gate{i} physical accepted) {proof})'
   reverse=f'(cons_zero (clause{i} physical holds) {reverse})'
  batch=f'gates{first//8:03d}';gateBatches.append(batch);gates=', '.join(f'{native}.gate{i}' for i in range(first,min(len(clauses),first+8)))
  cbatch=f'clauses{first//8:03d}';clauseBatches.append(cbatch);literals=', '.join(clause_at(i) for i in range(first,min(len(clauses),first+8)))
  text+=f'''theorem {batch} (physical : GKRAddress → F) (accepted : Holds {capture} physical) :
    ∀ gate ∈ [{gates}], gate.expressionResidual (fun index => physical addresses[index]) = 0 :=
  {proof}

theorem {cbatch} (physical : GKRAddress → F)
    (holds : {native}.artifact.LoweredHolds (fun index => physical addresses[index])) :
    ∀ clause ∈ [{literals}], clause.residual physical = 0 :=
  {reverse}
end {ns}
''';(directory/f'{part}.lean').write_text(text)
 text='module\npublic import Proven.KernelExact\n'+''.join(f'public import {imp}\n' for imp in imports)+f'''\n@[expose] public section
set_option warningAsError true
namespace {ns}
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option maxRecDepth 32768
'''
 pproof='(by intro index member; cases member)'
 for batch in reversed(placementBatches):pproof=f'(append_placements ({batch} physical logical agreement) {pproof})'
 gproof='(by intro gate member; cases member)'
 for batch in reversed(gateBatches):gproof=f'(append_holds ({batch} physical accepted) {gproof})'
 cproof='(show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)'
 for batch in reversed(clauseBatches):cproof=f'(append_zero ({batch} physical holds) {cproof})'
 text+=f'''/-- The checked typed relations supply every native scalar gate and cache. -/
theorem native_holds (physical : GKRAddress → F)
    (holds : {native}.artifact.LoweredHolds (fun index => physical addresses[index])) :
    Holds {capture} physical := by
  apply native_of_base (by kernel_rfl)
  kernel_exact {cproof}

/-- The typed source equations are exactly the imported description equations. -/
theorem description :
    {native}.artifact.source.map (fun expression => FlatOperation.assert (DescriptionBridge.toClean expression)) =
      Circuit.equations {capture} := by kernel_rfl

/-- Actual native gates and source placements imply every description equation. -/
theorem arithmetic : {title}CachedArithmeticClaim := by
  intro physical logical accepted agreement
  have gates : {native}.artifact.LoweredHolds (fun index => physical addresses[index]) :=
    {gproof}
  have bindings : ∀ index ∈ List.range {n}, placed physical logical index = logical index :=
    {pproof}
  have same : (fun index => physical addresses[{native}.artifact.placement index]) =
      (fun index => logical index.val) := by
    funext index
    simpa only [placed, dite_eq_left index.isLt] using
      bindings index.val (List.mem_range.mpr index.isLt)
  have source := {native}.artifact.backward {native}.selected {native}.extension
    {native}.certificate {native}.gatesChecked {native}.checked gates
  change {native}.artifact.SourceHolds
    (fun index => physical addresses[{native}.artifact.placement index]) at source
  rw [same] at source
  rw [← description]
  exact DescriptionBridge.assertions _ _ source
end {ns}
'''
 (directory.parent/(title+'.lean')).write_text(text)
 print(title,n,len(clauses),'arithmetic binding coordinates/gates')
