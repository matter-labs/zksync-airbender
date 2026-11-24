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
noncomputable def operand72 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 58))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 56))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 16⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions72 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 39])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 115])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup72 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions72⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields72 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 39])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 115])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values72 (logical : Nat → F) :
    (sourceExpressions72.map (Verification.environment logical)).toList = sourceFields72 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag72 (logical : Nat → F) :
    ((sourceFields72 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics72 (logical : Nat → F) :
    (sourceLookup72).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields72 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions72.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values72]
    exact source_tag72 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions72 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values72 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values72 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand73 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 59))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 57))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 17⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions73 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 40])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 116])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup73 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions73⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields73 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 40])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 116])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values73 (logical : Nat → F) :
    (sourceExpressions73.map (Verification.environment logical)).toList = sourceFields73 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag73 (logical : Nat → F) :
    ((sourceFields73 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics73 (logical : Nat → F) :
    (sourceLookup73).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields73 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions73.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values73]
    exact source_tag73 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions73 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values73 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values73 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand74 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 62))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 58))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 18⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions74 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 41])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 117])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup74 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions74⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields74 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 41])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 117])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values74 (logical : Nat → F) :
    (sourceExpressions74.map (Verification.environment logical)).toList = sourceFields74 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag74 (logical : Nat → F) :
    ((sourceFields74 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics74 (logical : Nat → F) :
    (sourceLookup74).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields74 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions74.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values74]
    exact source_tag74 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions74 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values74 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values74 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand75 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 63))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 59))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 19⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions75 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 42])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 118])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup75 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions75⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields75 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 42])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 118])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values75 (logical : Nat → F) :
    (sourceExpressions75.map (Verification.environment logical)).toList = sourceFields75 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag75 (logical : Nat → F) :
    ((sourceFields75 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics75 (logical : Nat → F) :
    (sourceLookup75).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields75 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions75.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values75]
    exact source_tag75 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions75 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values75 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values75 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand76 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 66))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 60))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 20⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions76 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 43])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 119])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup76 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions76⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields76 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 43])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 119])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values76 (logical : Nat → F) :
    (sourceExpressions76.map (Verification.environment logical)).toList = sourceFields76 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag76 (logical : Nat → F) :
    ((sourceFields76 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics76 (logical : Nat → F) :
    (sourceLookup76).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields76 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions76.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values76]
    exact source_tag76 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions76 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values76 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values76 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand77 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 67))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 61))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 21⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions77 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 44])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 120])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup77 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions77⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields77 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 44])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 120])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values77 (logical : Nat → F) :
    (sourceExpressions77.map (Verification.environment logical)).toList = sourceFields77 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag77 (logical : Nat → F) :
    ((sourceFields77 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics77 (logical : Nat → F) :
    (sourceLookup77).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields77 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions77.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values77]
    exact source_tag77 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions77 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values77 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values77 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand78 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 70))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 62))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 22⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions78 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 45])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 121])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup78 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions78⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields78 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 45])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 121])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values78 (logical : Nat → F) :
    (sourceExpressions78.map (Verification.environment logical)).toList = sourceFields78 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag78 (logical : Nat → F) :
    ((sourceFields78 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics78 (logical : Nat → F) :
    (sourceLookup78).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields78 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions78.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values78]
    exact source_tag78 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions78 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values78 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values78 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand79 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 71))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 63))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 23⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions79 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 46])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 122])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup79 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions79⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields79 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 46])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 122])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values79 (logical : Nat → F) :
    (sourceExpressions79.map (Verification.environment logical)).toList = sourceFields79 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag79 (logical : Nat → F) :
    ((sourceFields79 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics79 (logical : Nat → F) :
    (sourceLookup79).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields79 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions79.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values79]
    exact source_tag79 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions79 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values79 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values79 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand80 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 74))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 64))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 24⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions80 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 47])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 123])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup80 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions80⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields80 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 47])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 123])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values80 (logical : Nat → F) :
    (sourceExpressions80.map (Verification.environment logical)).toList = sourceFields80 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag80 (logical : Nat → F) :
    ((sourceFields80 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics80 (logical : Nat → F) :
    (sourceLookup80).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields80 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions80.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values80]
    exact source_tag80 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions80 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values80 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values80 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand81 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 75))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 65))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 25⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions81 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 48])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 124])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup81 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions81⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields81 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 48])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 124])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values81 (logical : Nat → F) :
    (sourceExpressions81.map (Verification.environment logical)).toList = sourceFields81 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag81 (logical : Nat → F) :
    ((sourceFields81 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics81 (logical : Nat → F) :
    (sourceLookup81).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields81 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions81.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values81]
    exact source_tag81 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions81 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values81 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values81 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand82 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 78))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 66))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 26⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions82 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 49])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 125])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup82 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions82⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields82 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 49])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 125])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values82 (logical : Nat → F) :
    (sourceExpressions82.map (Verification.environment logical)).toList = sourceFields82 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag82 (logical : Nat → F) :
    ((sourceFields82 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics82 (logical : Nat → F) :
    (sourceLookup82).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields82 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions82.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values82]
    exact source_tag82 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions82 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values82 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values82 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand83 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 79))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 67))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 27⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions83 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 50])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 126])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup83 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions83⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields83 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 50])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 126])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values83 (logical : Nat → F) :
    (sourceExpressions83.map (Verification.environment logical)).toList = sourceFields83 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag83 (logical : Nat → F) :
    ((sourceFields83 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics83 (logical : Nat → F) :
    (sourceLookup83).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields83 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions83.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values83]
    exact source_tag83 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions83 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values83 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values83 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.Bigint
