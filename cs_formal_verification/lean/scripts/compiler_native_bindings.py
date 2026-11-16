#!/usr/bin/env python3
"""Emit complete native sparse gate and placement bindings. The kernel checks every equality."""
from pathlib import Path
import json,re,sys
root=Path(__file__).resolve().parents[1]
families={'AddSub':'add-sub','Bigint':'bigint','BlakeG':'blake-g','BlakeRound':'blake-round','JumpBranch':'jump-branch','Keccak':'keccak','MulDiv':'mul-div','ShiftBinop':'shift-binop','SubwordMemory':'subword-memory','Unified':'unified','WordMemory':'word-memory'}
base={'LinearBaseFieldRelation','MaxQuadratic','EnforceSingleMaxQuadraticConstraint','CopyInBaseField','MaterializeSingleLookupInput'}
for family in sys.argv[1:] or families:
 c=json.load((root/f'artifacts/compiler/{families[family]}-cached.json').open())['circuit']
 ns=f'Airbender.Compiler.NativeBindings.{family}'
 native=f'Airbender.Compiler.FullArithmeticNative.{family}Cached.native'
 clean=f'Airbender.Compiler.CleanArithmeticNative.{family}Cached.native'
 capture=f'Airbender.Compiler.Captures.{family}.imported.circuit'
 large=family in {'Bigint','BlakeRound','Keccak'}
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
 placement_header=header
 if large:
  placementData=f"Airbender.Compiler.Captures.{family}.importedPlacementEntries"
  data=f'''module
public import Proven.KernelRfl
public import Human.Compiler.Captures.{family}

@[expose] public section
set_option warningAsError true
namespace {ns}
/-- The imported capture retains its shared literal placement array. -/
theorem placement_entries : ({capture}).placement_data.entries = {placementData} := by kernel_rfl
end {ns}
'''
  (directory/'PlacementData.lean').write_text(data)
  placement_header=header.replace('public import Proven.Compiler.NativeBridge',
    f'public import Proven.Compiler.NativeBridge\npublic import Proven.Compiler.NativeBindings.{family}.PlacementData')
 clauses=[]
 for li,l in enumerate(c['layers']):
  for ci,(output,rel) in enumerate(l['cached_relations']):
   if 'SingleColumnLookup' in rel: clauses.append(('cache',li,ci))
 for li,l in enumerate(c['layers']):
  for gi,g in enumerate(l['gates']+l['gates_with_external_connections']):
   if next(iter(g['enforced_relation'])) in base: clauses.append(('gate',li,gi))
 if family == 'BlakeRound':
  foundation=root/'proven/Proven/GKRProtocol/FullArithmeticNative/BlakeRoundCachedFoundation'
  definitions={}; bank_size=None; address_parts={}
  for path in sorted(foundation.glob('Part*.lean')):
   text=path.read_text()
   for part in re.finditer(r'(?s)def native\.addresses\.part(\d+) : List GKRAddress := \[(.*?)\]',text):
    address_parts[int(part[1])]=[entry.strip() for entry in part[2].split(',')]
   match=re.search(r'def native.bank : WireBank (\d+)',text)
   if match: bank_size=int(match[1])
   for match in re.finditer(r'(?ms)^def (native\.gate\d+|sharedExpression\d+)\b(.*?)(?=^(?:def|theorem|noncomputable|end|namespace|open|set_option)\b|\Z)',text):
    definitions[match[1]]=match[2]
  assert bank_size is not None
  addresses=[entry for part in sorted(address_parts) for entry in address_parts[part]]
  assert len(addresses)==bank_size
  def argument(text):
   text=text.lstrip()
   if text[0] in '(⟨[':
    closing={'(':')','⟨':'⟩','[':']'}[text[0]]; depth=0
    for index,char in enumerate(text):
     if char==text[0]:depth+=1
     if char==closing:depth-=1
     if depth==0:return text[:index+1],text[index+1:]
    raise ValueError('Unclosed native expression')
   value=re.match(r'[\w.]+',text)[0]
   return value,text[len(value):]
  def dependencies(name,seen=None):
   seen=set() if seen is None else seen
   if name in seen:return set(),set()
   seen.add(name); text=definitions[name]
   if name.startswith('native.gate'):
    if 'Compiler.ArithmeticGate.assertZero' in text:
     text,_=argument(text.split('Compiler.ArithmeticGate.assertZero',1)[1])
    elif 'Compiler.ArithmeticGate.define' in text:
     output,rest=argument(text.split('Compiler.ArithmeticGate.define',1)[1])
     expression,_=argument(rest);text=output+' '+expression
   wires={int(value) for value in re.findall(r'⟨(\d+), by decide⟩',text)}
   shared=set(re.findall(r'\bsharedExpression\d+\b',text))
   for child in tuple(shared):
    child_wires,child_shared=dependencies(child,seen)
    wires |= child_wires;shared |= child_shared
   return wires,shared
  required_wires=sorted(set().union(*(dependencies(f'native.gate{index}')[0] for index in range(len(clauses)))))
  bank_modules=[]
  for first in range(0,len(required_wires),32):
   name=f'Bank{first//32:03d}';bank_modules.append(name)
   text=f'''module
public import Proven.Compiler.NativeBridge
public import Proven.GKRProtocol.FullArithmeticNative.{family}Cached
@[expose] public section
set_option warningAsError true
namespace {ns}
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768
'''
   for index in required_wires[first:first+32]:
    text+=f'''/-- This bank coordinate has a checked literal lookup. -/
theorem coordinate{index} : {native}.bank.address ⟨{index}, by decide⟩ = {addresses[index]} :=
  bank_lookup {native}.addresses (by decide) ⟨{index}, by decide⟩ ({addresses[index]}) (by cbv)
'''
   (directory/f'{name}.lean').write_text(text+f'end {ns}\n')
  for obsolete in directory.glob('Bank[0-9][0-9][0-9].lean'):
   if obsolete.stem not in bank_modules:obsolete.unlink()
  (directory/'BankCoordinates.lean').write_text('module\n'+''.join(f'public import Proven.Compiler.NativeBindings.{family}.{name}\n' for name in bank_modules))
  gates=',\n  '.join(f'{native}.gate{index}' for index in range(len(clauses)))
  attributes=''.join('attribute [cbv_opaque] '+' '.join(f'{native}.gate{index}' for index in range(first,min(first+8,len(clauses))))+'\n' for first in range(0,len(clauses),8))
  text=f'''module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Proven.GKRProtocol.FullArithmeticNative.{family}Cached
@[expose] public section
set_option warningAsError true
namespace {ns}
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768
{attributes}
/-- The scalar gate list retains the native gate constants. -/
def scalar_gate_data : List (ArithmeticGate {bank_size} Source.BaseField) := [
  {gates}]
theorem scalar_gate_data_binding : {native}.artifact.gates = scalar_gate_data := by kernel_rfl
theorem scalar_gate_data_checked : scalar_gate_data.all ArithmeticGate.check = true :=
  (congrArg (fun items => items.all ArithmeticGate.check) scalar_gate_data_binding).symm.trans {native}.gatesChecked
end {ns}
'''
  (directory/'NativeData.lean').write_text(text)
  text=f'''module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.{family}
@[expose] public section
set_option warningAsError true
namespace {ns}
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768
'''
  for li,layer in enumerate(c['layers']):
   for field,label in [('gates','Gates'),('cached_relations','Caches')]:
    count=len(layer[field])
    if count <= 253:continue
    literal=f'Airbender.Compiler.Captures.{family}.importedLayer{li}{label}'
    for first in range(0,count,8):
     text+='attribute [cbv_opaque] '+' '.join(f'{literal}Entry{index}' for index in range(first,min(first+8,count)))+'\n'
    actual=f'(({capture}).layers[{li}]\'(by decide)).{field}'
    if field=='gates':
     assert not layer['gates_with_external_connections']
     external=f'(({capture}).layers[{li}]\'(by decide)).gates_with_external_connections'
     text+=f'''theorem layer{li}_gates : {actual} ++ {external} = {literal} := by
  have empty : {external} = #[] := by kernel_rfl
  have binding : {actual} = {literal} := by kernel_rfl
  simpa only [empty, Array.append_empty] using binding
'''
    else:
     text+=f'theorem layer{li}_caches : {actual} = {literal} := by kernel_rfl\n'
  (directory/'CaptureData.lean').write_text(text+f'end {ns}\n')
  header=header.replace('public import Proven.Compiler.NativeBridge',
   'public import Proven.Compiler.NativeLiteralBridge\n'+''.join(f'public import Proven.Compiler.NativeBindings.{family}.{name}\n' for name in ['NativeData','BankCoordinates','CaptureData']).rstrip())
 imports=[];batches=[]
 gate_step=8 if family=="BlakeRound" else 16
 for first in range(0,len(clauses),gate_step):
  name=f'Gates{first//gate_step:03d}';imports.append(f'Proven.Compiler.NativeBindings.{family}.{name}')
  s=header
  for i in range(first,min(first+gate_step,len(clauses))):
   kind,li,idx=clauses[i]
   layer=f'({capture}).layers[{li}]\'(by decide)'
   if kind=='cache':
    entry=f'({layer}).cached_relations[{idx}]\'(by decide)'
    clause=f'(Clause.cache ({entry}).1 ({entry}).2)'
   else:
    entry=f'(({layer}).gates ++ ({layer}).gates_with_external_connections)[{idx}]\'(by decide)'
    clause=f'(Clause.gate ({entry}).enforced_relation)'
   if family == 'BlakeRound':
    field='cached_relations' if kind=='cache' else 'gates'
    large_field=len(c['layers'][li][field]) > 253
    capture_proof=''
    if large_field:
     label='Caches' if kind=='cache' else 'Gates'
     literal=f'Airbender.Compiler.Captures.{family}.importedLayer{li}{label}Entry{idx}'
     capture_proof=f'''  have captured : {entry} = {literal} :=
    entry_of_binding (by decide) layer{li}_{'caches' if kind=='cache' else 'gates'} (by cbv)
'''
     clause=f'(Clause.cache ({literal}).1 ({literal}).2)' if kind=='cache' else f'(Clause.gate ({literal}).enforced_relation)'
    wires,shared=dependencies(f'native.gate{i}')
    simplifications=['sparseResidual',f'{native}.gate{i}']+[f'Airbender.Compiler.FullArithmeticNative.{family}Cached.{name}' for name in sorted(shared)]+([] if 'Compiler.ArithmeticGate.copy' in definitions[f'native.gate{i}'] else ['Expression.value'])+(['Function.comp_apply'] if wires else [])+[f'coordinate{index}' for index in sorted(wires)]
    s+=f'''
/-- The actual native sparse relation supplies gate {i}. -/
theorem gate{i} (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds {capture} physical) :
    {native}.gate{i}.expressionResidual (physical ∘ {native}.bank.address) = 0 := by
  have checked : {native}.gate{i}.check = true :=
    all_at (index := {i}) (value := {native}.gate{i}) scalar_gate_data_checked (by cbv)
{capture_proof}  have binding : sparseResidual {native}.gate{i} (physical ∘ {native}.bank.address) =
      {clause}.residual physical := by
    simp only [{', '.join(simplifications)}]
    rfl
'''
    if large_field:
     s+=f'  have acceptedEntry := {kind}_at_literal accepted ⟨{li}, by decide⟩ ⟨{idx}, by decide⟩ {literal} captured\n'
    else:
     s+=f'  have acceptedEntry := {kind}_at accepted ⟨{li}, by decide⟩ ⟨{idx}, by decide⟩\n'
    s+='  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)\n'
    continue
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
  gates=', '.join(f'{native}.gate{i}' for i in range(first,min(first+gate_step,len(clauses))))
  batch=f'gates{first//gate_step:03d}';batches.append(batch)
  proof='(by intro gate member; cases member)'
  for i in reversed(range(first,min(first+gate_step,len(clauses)))): proof=f'(cons_holds (gate{i} physical accepted) {proof})'
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
  s=placement_header
  for i in range(first,min(first+placement_step,count)):
   if large:
    kind,value=next(iter(c['placement_data'][str(i)].items()))
    address=f'(GKRAddress.{kind} {value["layer"]} {value["offset"]})' if isinstance(value,dict) else f'(GKRAddress.{kind} {value})'
    s+=f'''
/-- Logical column {i} uses its actual native placement. -/
theorem placement{i} (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement {capture} physical logical) :
    ({clean}.environment physical (Verification.environment logical).data).get {i} = logical {i} := by
  have included := Array.getElem_mem (xs := ({capture}).placement_data.entries) (i := {i}) (by decide)
  have captured : ({capture}).placement_data.entries[{i}]'(by decide) = ({i}, {address}) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : {clean}.placement {i} = {native}.bank.placement {address} := by
    as_aux_lemma => kernel_rfl
  have inverse : {native}.bank.address ({native}.bank.placement {address}) = {address} :=
    of_decide_eq_true {clean}.placementInBank{i}
  exact (congrArg physical ((congrArg {native}.bank.address selected).trans inverse)).trans same.symm
'''
    continue
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
