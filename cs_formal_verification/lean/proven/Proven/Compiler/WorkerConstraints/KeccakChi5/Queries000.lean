module
public import Proven.Compiler.WorkerConstraints.Values
public import Proven.Compiler.WorkerConstraints.Setup
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakChi5
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One actual resolved primitive operand. -/
noncomputable def operand0 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1073741824, by decide⟩⟩, (.BaseLayerMemory 64)), (⟨⟨939524097, by decide⟩⟩, (.BaseLayerMemory 63))], ⟨⟨0, by decide⟩⟩⟩, 0⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions0 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741824, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨939524097, by decide⟩⟩, .Var 0])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup0 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions0⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields0 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741824, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨939524097, by decide⟩⟩, .Var 0])])).eval (Verification.environment logical)]

theorem source_values0 (logical : Nat → F) :
    (sourceExpressions0.map (Verification.environment logical)).toList = sourceFields0 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics0 (logical : Nat → F) :
    (sourceLookup0).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields0 logical = NativeWorkerSetup.rows .chi5 2 index := by
  simpa only [sourceLookup0, sourceExpressions0, sourceFields0, Trace.timestampLookup] using
    timestamp_refinement .chi5 (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741824, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨939524097, by decide⟩⟩, .Var 0])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand1 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 2))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 63))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 4))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 12))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 23))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 34))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 45))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 56))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 0))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1610612596, by decide⟩⟩⟩], 0⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions1 : Vector (Airbender.Expression F) 11 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 3])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 0])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 5])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 7])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 8])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 9])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 10])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 11])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 54])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1610612596, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup1 : Lookup F := ⟨(WorkerConstraints.setupTable .chi5).toRaw, sourceExpressions1⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields1 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 3])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 0])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 5])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 7])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 8])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 9])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 10])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 11])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 54])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1610612596, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values1 (logical : Nat → F) :
    (sourceExpressions1.map (Verification.environment logical)).toList = sourceFields1 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag1 (logical : Nat → F) :
    ((sourceFields1 logical)[10]?).getD 0 ≠ 0 := by
  change (66 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics1 (logical : Nat → F) :
    (sourceLookup1).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields1 logical = NativeWorkerSetup.rows .chi5 0 index := by
  have tag : (((sourceExpressions1.map (Verification.environment logical)).toList)[width .chi5 - 1]?).getD 0 ≠ 0 := by
    rw [source_values1]
    exact source_tag1 logical
  have equivalent := generic_lookup_refinement .chi5 sourceExpressions1 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values1 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values1 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand2 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 1))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 13))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 25))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 37))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 49))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 61))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 73))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 85))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 97))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 109))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177142, by decide⟩⟩⟩], 1⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions2 : Vector (Airbender.Expression F) 11 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 55])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 67])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 79])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 91])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 103])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 115])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 127])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 139])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 151])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 163])]), Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup2 : Lookup F := ⟨(WorkerConstraints.setupTable .chi5).toRaw, sourceExpressions2⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields2 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 55])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 67])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 79])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 91])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 103])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 115])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 127])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 139])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 151])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 163])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values2 (logical : Nat → F) :
    (sourceExpressions2.map (Verification.environment logical)).toList = sourceFields2 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag2 (logical : Nat → F) :
    ((sourceFields2 logical)[10]?).getD 0 ≠ 0 := by
  change (65 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics2 (logical : Nat → F) :
    (sourceLookup2).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields2 logical = NativeWorkerSetup.rows .chi5 0 index := by
  have tag : (((sourceExpressions2.map (Verification.environment logical)).toList)[width .chi5 - 1]?).getD 0 ≠ 0 := by
    rw [source_values2]
    exact source_tag2 logical
  have equivalent := generic_lookup_refinement .chi5 sourceExpressions2 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values2 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values2 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand3 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 2))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 14))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 26))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 38))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 50))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 62))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 74))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 86))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 98))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 110))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177142, by decide⟩⟩⟩], 2⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions3 : Vector (Airbender.Expression F) 11 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 56])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 68])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 80])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 92])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 104])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 116])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 128])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 140])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 152])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 164])]), Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup3 : Lookup F := ⟨(WorkerConstraints.setupTable .chi5).toRaw, sourceExpressions3⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields3 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 56])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 68])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 80])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 92])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 104])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 116])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 128])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 140])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 152])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 164])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values3 (logical : Nat → F) :
    (sourceExpressions3.map (Verification.environment logical)).toList = sourceFields3 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag3 (logical : Nat → F) :
    ((sourceFields3 logical)[10]?).getD 0 ≠ 0 := by
  change (65 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics3 (logical : Nat → F) :
    (sourceLookup3).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields3 logical = NativeWorkerSetup.rows .chi5 0 index := by
  have tag : (((sourceExpressions3.map (Verification.environment logical)).toList)[width .chi5 - 1]?).getD 0 ≠ 0 := by
    rw [source_values3]
    exact source_tag3 logical
  have equivalent := generic_lookup_refinement .chi5 sourceExpressions3 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values3 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values3 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand4 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 3))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 15))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 27))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 39))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 51))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 63))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 75))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 87))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 99))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 111))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177142, by decide⟩⟩⟩], 3⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions4 : Vector (Airbender.Expression F) 11 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 57])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 69])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 81])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 93])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 105])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 117])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 129])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 141])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 153])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 165])]), Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup4 : Lookup F := ⟨(WorkerConstraints.setupTable .chi5).toRaw, sourceExpressions4⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields4 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 57])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 69])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 81])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 93])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 105])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 117])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 129])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 141])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 153])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 165])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values4 (logical : Nat → F) :
    (sourceExpressions4.map (Verification.environment logical)).toList = sourceFields4 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag4 (logical : Nat → F) :
    ((sourceFields4 logical)[10]?).getD 0 ≠ 0 := by
  change (65 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics4 (logical : Nat → F) :
    (sourceLookup4).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields4 logical = NativeWorkerSetup.rows .chi5 0 index := by
  have tag : (((sourceExpressions4.map (Verification.environment logical)).toList)[width .chi5 - 1]?).getD 0 ≠ 0 := by
    rw [source_values4]
    exact source_tag4 logical
  have equivalent := generic_lookup_refinement .chi5 sourceExpressions4 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values4 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values4 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand5 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 10)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 1)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 2)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 3))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 21)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 13)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 14)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 15))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 32)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 25)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 26)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 27))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 43)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 37)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 38)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 39))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 54)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 49)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 50)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 51))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 13)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 61)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 62)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 63))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 24)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 73)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 74)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 75))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 35)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 85)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 86)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 87))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 46)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 97)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 98)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 99))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 57)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 109)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 110)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 111))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177142, by decide⟩⟩⟩], 4⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions5 : Vector (Airbender.Expression F) 11 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 14]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 55]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 56]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 57])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 22]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 67]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 68]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 69])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 30]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 79]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 80]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 81])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 38]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 91]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 92]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 93])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 46]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 103]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 104]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 105])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 16]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 115]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 116]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 117])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 24]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 127]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 128]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 129])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 32]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 139]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 140]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 141])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 40]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 151]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 152]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 153])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 48]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 163]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 164]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 165])]), Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup5 : Lookup F := ⟨(WorkerConstraints.setupTable .chi5).toRaw, sourceExpressions5⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields5 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 14]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 55]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 56]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 57])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 22]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 67]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 68]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 69])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 30]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 79]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 80]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 81])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 38]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 91]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 92]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 93])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 46]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 103]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 104]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 105])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 16]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 115]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 116]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 117])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 24]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 127]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 128]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 129])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 32]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 139]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 140]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 141])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 40]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 151]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 152]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 153])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 48]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 163]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 164]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 165])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values5 (logical : Nat → F) :
    (sourceExpressions5.map (Verification.environment logical)).toList = sourceFields5 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag5 (logical : Nat → F) :
    ((sourceFields5 logical)[10]?).getD 0 ≠ 0 := by
  change (65 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics5 (logical : Nat → F) :
    (sourceLookup5).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields5 logical = NativeWorkerSetup.rows .chi5 0 index := by
  have tag : (((sourceExpressions5.map (Verification.environment logical)).toList)[width .chi5 - 1]?).getD 0 ≠ 0 := by
    rw [source_values5]
    exact source_tag5 logical
  have equivalent := generic_lookup_refinement .chi5 sourceExpressions5 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values5 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values5 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand6 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 4))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 16))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 28))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 40))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 52))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 64))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 76))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 88))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 100))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 112))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177142, by decide⟩⟩⟩], 5⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions6 : Vector (Airbender.Expression F) 11 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 58])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 70])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 82])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 94])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 106])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 118])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 130])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 142])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 154])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 166])]), Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup6 : Lookup F := ⟨(WorkerConstraints.setupTable .chi5).toRaw, sourceExpressions6⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields6 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 58])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 70])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 82])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 94])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 106])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 118])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 130])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 142])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 154])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 166])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values6 (logical : Nat → F) :
    (sourceExpressions6.map (Verification.environment logical)).toList = sourceFields6 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag6 (logical : Nat → F) :
    ((sourceFields6 logical)[10]?).getD 0 ≠ 0 := by
  change (65 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics6 (logical : Nat → F) :
    (sourceLookup6).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields6 logical = NativeWorkerSetup.rows .chi5 0 index := by
  have tag : (((sourceExpressions6.map (Verification.environment logical)).toList)[width .chi5 - 1]?).getD 0 ≠ 0 := by
    rw [source_values6]
    exact source_tag6 logical
  have equivalent := generic_lookup_refinement .chi5 sourceExpressions6 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values6 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values6 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand7 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 5))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 17))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 29))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 41))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 53))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 65))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 77))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 89))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 101))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 113))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177142, by decide⟩⟩⟩], 6⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions7 : Vector (Airbender.Expression F) 11 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 59])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 71])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 83])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 95])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 107])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 119])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 131])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 143])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 155])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 167])]), Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup7 : Lookup F := ⟨(WorkerConstraints.setupTable .chi5).toRaw, sourceExpressions7⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields7 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 59])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 71])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 83])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 95])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 107])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 119])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 131])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 143])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 155])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 167])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values7 (logical : Nat → F) :
    (sourceExpressions7.map (Verification.environment logical)).toList = sourceFields7 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag7 (logical : Nat → F) :
    ((sourceFields7 logical)[10]?).getD 0 ≠ 0 := by
  change (65 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics7 (logical : Nat → F) :
    (sourceLookup7).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields7 logical = NativeWorkerSetup.rows .chi5 0 index := by
  have tag : (((sourceExpressions7.map (Verification.environment logical)).toList)[width .chi5 - 1]?).getD 0 ≠ 0 := by
    rw [source_values7]
    exact source_tag7 logical
  have equivalent := generic_lookup_refinement .chi5 sourceExpressions7 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values7 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values7 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand8 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 6))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 18))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 30))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 42))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 54))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 66))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 78))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 90))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 102))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 114))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177142, by decide⟩⟩⟩], 7⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions8 : Vector (Airbender.Expression F) 11 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 60])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 72])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 96])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 108])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 120])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 132])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 144])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 156])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 168])]), Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup8 : Lookup F := ⟨(WorkerConstraints.setupTable .chi5).toRaw, sourceExpressions8⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields8 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 60])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 72])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 96])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 108])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 120])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 132])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 144])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 156])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 168])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values8 (logical : Nat → F) :
    (sourceExpressions8.map (Verification.environment logical)).toList = sourceFields8 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag8 (logical : Nat → F) :
    ((sourceFields8 logical)[10]?).getD 0 ≠ 0 := by
  change (65 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics8 (logical : Nat → F) :
    (sourceLookup8).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields8 logical = NativeWorkerSetup.rows .chi5 0 index := by
  have tag : (((sourceExpressions8.map (Verification.environment logical)).toList)[width .chi5 - 1]?).getD 0 ≠ 0 := by
    rw [source_values8]
    exact source_tag8 logical
  have equivalent := generic_lookup_refinement .chi5 sourceExpressions8 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values8 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values8 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand9 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 11)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 4)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 5)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 6))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 22)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 16)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 17)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 18))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 33)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 28)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 29)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 30))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 44)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 40)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 41)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 42))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 55)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 52)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 53)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 54))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 14)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 64)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 65)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 66))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 25)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 76)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 77)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 78))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 36)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 88)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 89)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 90))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 47)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 100)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 101)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 102))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 58)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 112)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 113)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 114))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177142, by decide⟩⟩⟩], 8⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions9 : Vector (Airbender.Expression F) 11 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 15]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 58]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 59]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 60])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 23]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 70]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 71]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 72])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 31]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 82]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 83]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 84])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 39]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 94]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 95]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 96])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 47]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 106]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 107]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 108])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 17]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 118]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 119]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 120])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 25]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 130]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 131]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 132])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 33]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 142]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 143]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 144])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 41]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 154]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 155]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 156])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 49]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 166]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 167]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 168])]), Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup9 : Lookup F := ⟨(WorkerConstraints.setupTable .chi5).toRaw, sourceExpressions9⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields9 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 15]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 58]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 59]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 60])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 23]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 70]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 71]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 72])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 31]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 82]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 83]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 84])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 39]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 94]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 95]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 96])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 47]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 106]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 107]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 108])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 17]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 118]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 119]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 120])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 25]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 130]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 131]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 132])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 33]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 142]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 143]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 144])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 41]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 154]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 155]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 156])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 49]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 166]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 167]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 168])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values9 (logical : Nat → F) :
    (sourceExpressions9.map (Verification.environment logical)).toList = sourceFields9 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag9 (logical : Nat → F) :
    ((sourceFields9 logical)[10]?).getD 0 ≠ 0 := by
  change (65 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics9 (logical : Nat → F) :
    (sourceLookup9).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields9 logical = NativeWorkerSetup.rows .chi5 0 index := by
  have tag : (((sourceExpressions9.map (Verification.environment logical)).toList)[width .chi5 - 1]?).getD 0 ≠ 0 := by
    rw [source_values9]
    exact source_tag9 logical
  have equivalent := generic_lookup_refinement .chi5 sourceExpressions9 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values9 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values9 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand10 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 7))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 19))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 31))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 43))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 55))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 67))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 79))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 91))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 103))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 115))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177142, by decide⟩⟩⟩], 9⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions10 : Vector (Airbender.Expression F) 11 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 61])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 73])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 97])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 109])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 121])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 133])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 145])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 157])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 169])]), Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup10 : Lookup F := ⟨(WorkerConstraints.setupTable .chi5).toRaw, sourceExpressions10⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields10 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 61])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 73])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 97])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 109])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 121])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 133])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 145])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 157])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 169])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values10 (logical : Nat → F) :
    (sourceExpressions10.map (Verification.environment logical)).toList = sourceFields10 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag10 (logical : Nat → F) :
    ((sourceFields10 logical)[10]?).getD 0 ≠ 0 := by
  change (65 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics10 (logical : Nat → F) :
    (sourceLookup10).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields10 logical = NativeWorkerSetup.rows .chi5 0 index := by
  have tag : (((sourceExpressions10.map (Verification.environment logical)).toList)[width .chi5 - 1]?).getD 0 ≠ 0 := by
    rw [source_values10]
    exact source_tag10 logical
  have equivalent := generic_lookup_refinement .chi5 sourceExpressions10 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values10 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values10 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand11 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 8))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 20))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 32))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 44))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 56))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 68))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 80))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 92))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 104))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 116))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177142, by decide⟩⟩⟩], 10⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions11 : Vector (Airbender.Expression F) 11 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 62])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 74])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 86])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 98])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 110])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 122])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 134])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 146])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 158])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 170])]), Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup11 : Lookup F := ⟨(WorkerConstraints.setupTable .chi5).toRaw, sourceExpressions11⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields11 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 62])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 74])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 86])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 98])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 110])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 122])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 134])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 146])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 158])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 170])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values11 (logical : Nat → F) :
    (sourceExpressions11.map (Verification.environment logical)).toList = sourceFields11 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag11 (logical : Nat → F) :
    ((sourceFields11 logical)[10]?).getD 0 ≠ 0 := by
  change (65 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics11 (logical : Nat → F) :
    (sourceLookup11).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields11 logical = NativeWorkerSetup.rows .chi5 0 index := by
  have tag : (((sourceExpressions11.map (Verification.environment logical)).toList)[width .chi5 - 1]?).getD 0 ≠ 0 := by
    rw [source_values11]
    exact source_tag11 logical
  have equivalent := generic_lookup_refinement .chi5 sourceExpressions11 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values11 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values11 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.KeccakChi5
