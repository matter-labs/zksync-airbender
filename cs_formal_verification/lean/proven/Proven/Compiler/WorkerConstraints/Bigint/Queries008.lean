module
public import Proven.Compiler.WorkerConstraints.Values
public import Proven.Compiler.WorkerConstraints.Setup
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One actual resolved primitive operand. -/
noncomputable def operand96 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 78)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 110))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088587, by decide⟩⟩⟩], 40⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions96 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 137]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 169])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088587, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup96 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions96⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields96 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 137]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 169])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088587, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values96 (logical : Nat → F) :
    (sourceExpressions96.map (Verification.environment logical)).toList = sourceFields96 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag96 (logical : Nat → F) :
    ((sourceFields96 logical)[2]?).getD 0 ≠ 0 := by
  change (25 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics96 (logical : Nat → F) :
    (sourceLookup96).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields96 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions96.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values96]
    exact source_tag96 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions96 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values96 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values96 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand97 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 79)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 111))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088587, by decide⟩⟩⟩], 41⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions97 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 138]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 170])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088587, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup97 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions97⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields97 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 138]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 170])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088587, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values97 (logical : Nat → F) :
    (sourceExpressions97.map (Verification.environment logical)).toList = sourceFields97 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag97 (logical : Nat → F) :
    ((sourceFields97 logical)[2]?).getD 0 ≠ 0 := by
  change (25 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics97 (logical : Nat → F) :
    (sourceLookup97).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields97 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions97.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values97]
    exact source_tag97 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions97 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values97 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values97 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand98 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 95)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 127))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088587, by decide⟩⟩⟩], 42⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions98 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 154]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 186])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088587, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup98 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions98⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields98 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 154]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 186])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088587, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values98 (logical : Nat → F) :
    (sourceExpressions98.map (Verification.environment logical)).toList = sourceFields98 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag98 (logical : Nat → F) :
    ((sourceFields98 logical)[2]?).getD 0 ≠ 0 := by
  change (25 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics98 (logical : Nat → F) :
    (sourceLookup98).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields98 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions98.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values98]
    exact source_tag98 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions98 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values98 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values98 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand99 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 96)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 128))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088587, by decide⟩⟩⟩], 43⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions99 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 155]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 187])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088587, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup99 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions99⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields99 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 155]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 187])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088587, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values99 (logical : Nat → F) :
    (sourceExpressions99.map (Verification.environment logical)).toList = sourceFields99 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag99 (logical : Nat → F) :
    ((sourceFields99 logical)[2]?).getD 0 ≠ 0 := by
  change (25 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics99 (logical : Nat → F) :
    (sourceLookup99).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields99 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions99.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values99]
    exact source_tag99 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions99 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values99 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values99 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand100 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 97)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 129))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088587, by decide⟩⟩⟩], 44⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions100 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 156]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 188])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088587, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup100 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions100⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields100 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 156]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 188])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088587, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values100 (logical : Nat → F) :
    (sourceExpressions100.map (Verification.environment logical)).toList = sourceFields100 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag100 (logical : Nat → F) :
    ((sourceFields100 logical)[2]?).getD 0 ≠ 0 := by
  change (25 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics100 (logical : Nat → F) :
    (sourceLookup100).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields100 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions100.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values100]
    exact source_tag100 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions100 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values100 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values100 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand101 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 98)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 130))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088587, by decide⟩⟩⟩], 45⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions101 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 157]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 189])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088587, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup101 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions101⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields101 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 157]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 189])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088587, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values101 (logical : Nat → F) :
    (sourceExpressions101.map (Verification.environment logical)).toList = sourceFields101 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag101 (logical : Nat → F) :
    ((sourceFields101 logical)[2]?).getD 0 ≠ 0 := by
  change (25 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics101 (logical : Nat → F) :
    (sourceLookup101).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields101 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions101.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values101]
    exact source_tag101 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions101 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values101 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values101 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand102 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 80)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 112))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524041, by decide⟩⟩⟩], 46⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions102 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 139]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 171])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup102 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions102⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields102 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 139]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 171])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values102 (logical : Nat → F) :
    (sourceExpressions102.map (Verification.environment logical)).toList = sourceFields102 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag102 (logical : Nat → F) :
    ((sourceFields102 logical)[2]?).getD 0 ≠ 0 := by
  change (26 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics102 (logical : Nat → F) :
    (sourceLookup102).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields102 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions102.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values102]
    exact source_tag102 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions102 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values102 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values102 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand103 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 81)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 113))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524041, by decide⟩⟩⟩], 47⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions103 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 140]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 172])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup103 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions103⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields103 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 140]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 172])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values103 (logical : Nat → F) :
    (sourceExpressions103.map (Verification.environment logical)).toList = sourceFields103 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag103 (logical : Nat → F) :
    ((sourceFields103 logical)[2]?).getD 0 ≠ 0 := by
  change (26 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics103 (logical : Nat → F) :
    (sourceLookup103).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields103 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions103.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values103]
    exact source_tag103 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions103 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values103 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values103 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand104 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 82)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 114))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524041, by decide⟩⟩⟩], 48⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions104 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 141]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 173])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup104 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions104⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields104 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 141]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 173])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values104 (logical : Nat → F) :
    (sourceExpressions104.map (Verification.environment logical)).toList = sourceFields104 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag104 (logical : Nat → F) :
    ((sourceFields104 logical)[2]?).getD 0 ≠ 0 := by
  change (26 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics104 (logical : Nat → F) :
    (sourceLookup104).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields104 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions104.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values104]
    exact source_tag104 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions104 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values104 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values104 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand105 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 83)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 115))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524041, by decide⟩⟩⟩], 49⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions105 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 142]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 174])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup105 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions105⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields105 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 142]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 174])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values105 (logical : Nat → F) :
    (sourceExpressions105.map (Verification.environment logical)).toList = sourceFields105 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag105 (logical : Nat → F) :
    ((sourceFields105 logical)[2]?).getD 0 ≠ 0 := by
  change (26 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics105 (logical : Nat → F) :
    (sourceLookup105).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields105 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions105.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values105]
    exact source_tag105 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions105 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values105 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values105 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand106 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 84)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 116))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524041, by decide⟩⟩⟩], 50⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions106 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 143]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 175])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup106 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions106⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields106 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 143]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 175])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values106 (logical : Nat → F) :
    (sourceExpressions106.map (Verification.environment logical)).toList = sourceFields106 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag106 (logical : Nat → F) :
    ((sourceFields106 logical)[2]?).getD 0 ≠ 0 := by
  change (26 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics106 (logical : Nat → F) :
    (sourceLookup106).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields106 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions106.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values106]
    exact source_tag106 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions106 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values106 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values106 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand107 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 85)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 117))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524041, by decide⟩⟩⟩], 51⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions107 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 144]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 176])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup107 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions107⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields107 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 144]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 176])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values107 (logical : Nat → F) :
    (sourceExpressions107.map (Verification.environment logical)).toList = sourceFields107 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag107 (logical : Nat → F) :
    ((sourceFields107 logical)[2]?).getD 0 ≠ 0 := by
  change (26 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics107 (logical : Nat → F) :
    (sourceLookup107).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields107 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions107.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values107]
    exact source_tag107 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions107 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values107 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values107 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.Bigint
