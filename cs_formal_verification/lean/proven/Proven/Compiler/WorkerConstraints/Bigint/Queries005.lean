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
noncomputable def operand60 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 18))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 44))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 4⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions60 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 13])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 103])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup60 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions60⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields60 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 13])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 103])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values60 (logical : Nat → F) :
    (sourceExpressions60.map (Verification.environment logical)).toList = sourceFields60 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag60 (logical : Nat → F) :
    ((sourceFields60 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics60 (logical : Nat → F) :
    (sourceLookup60).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields60 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions60.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values60]
    exact source_tag60 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions60 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values60 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values60 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand61 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 19))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 45))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 5⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions61 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 14])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 104])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup61 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions61⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields61 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 14])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 104])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values61 (logical : Nat → F) :
    (sourceExpressions61.map (Verification.environment logical)).toList = sourceFields61 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag61 (logical : Nat → F) :
    ((sourceFields61 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics61 (logical : Nat → F) :
    (sourceLookup61).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields61 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions61.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values61]
    exact source_tag61 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions61 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values61 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values61 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand62 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 46))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 6⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions62 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 17])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 105])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup62 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions62⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields62 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 17])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 105])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values62 (logical : Nat → F) :
    (sourceExpressions62.map (Verification.environment logical)).toList = sourceFields62 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag62 (logical : Nat → F) :
    ((sourceFields62 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics62 (logical : Nat → F) :
    (sourceLookup62).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields62 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions62.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values62]
    exact source_tag62 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions62 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values62 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values62 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand63 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 25))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 47))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 7⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions63 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 18])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 106])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup63 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions63⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields63 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 18])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 106])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values63 (logical : Nat → F) :
    (sourceExpressions63.map (Verification.environment logical)).toList = sourceFields63 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag63 (logical : Nat → F) :
    ((sourceFields63 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics63 (logical : Nat → F) :
    (sourceLookup63).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields63 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions63.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values63]
    exact source_tag63 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions63 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values63 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values63 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand64 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 30))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 48))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 8⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions64 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 21])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 107])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup64 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions64⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields64 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 21])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 107])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values64 (logical : Nat → F) :
    (sourceExpressions64.map (Verification.environment logical)).toList = sourceFields64 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag64 (logical : Nat → F) :
    ((sourceFields64 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics64 (logical : Nat → F) :
    (sourceLookup64).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields64 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions64.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values64]
    exact source_tag64 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions64 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values64 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values64 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand65 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 31))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 49))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 9⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions65 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 22])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 108])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup65 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions65⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields65 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 22])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 108])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values65 (logical : Nat → F) :
    (sourceExpressions65.map (Verification.environment logical)).toList = sourceFields65 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag65 (logical : Nat → F) :
    ((sourceFields65 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics65 (logical : Nat → F) :
    (sourceLookup65).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields65 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions65.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values65]
    exact source_tag65 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions65 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values65 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values65 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand66 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 36))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 50))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 10⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions66 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 25])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 109])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup66 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions66⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields66 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 25])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 109])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values66 (logical : Nat → F) :
    (sourceExpressions66.map (Verification.environment logical)).toList = sourceFields66 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag66 (logical : Nat → F) :
    ((sourceFields66 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics66 (logical : Nat → F) :
    (sourceLookup66).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields66 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions66.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values66]
    exact source_tag66 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions66 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values66 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values66 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand67 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 37))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 51))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 11⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions67 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 26])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 110])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup67 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions67⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields67 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 26])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 110])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values67 (logical : Nat → F) :
    (sourceExpressions67.map (Verification.environment logical)).toList = sourceFields67 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag67 (logical : Nat → F) :
    ((sourceFields67 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics67 (logical : Nat → F) :
    (sourceLookup67).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields67 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions67.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values67]
    exact source_tag67 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions67 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values67 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values67 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand68 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 42))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 52))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 12⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions68 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 29])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 111])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup68 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions68⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields68 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 29])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 111])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values68 (logical : Nat → F) :
    (sourceExpressions68.map (Verification.environment logical)).toList = sourceFields68 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag68 (logical : Nat → F) :
    ((sourceFields68 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics68 (logical : Nat → F) :
    (sourceLookup68).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields68 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions68.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values68]
    exact source_tag68 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions68 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values68 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values68 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand69 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 43))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 53))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 13⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions69 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 30])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 112])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup69 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions69⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields69 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 30])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 112])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values69 (logical : Nat → F) :
    (sourceExpressions69.map (Verification.environment logical)).toList = sourceFields69 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag69 (logical : Nat → F) :
    ((sourceFields69 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics69 (logical : Nat → F) :
    (sourceLookup69).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields69 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions69.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values69]
    exact source_tag69 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions69 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values69 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values69 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand70 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 48))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 54))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 14⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions70 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 33])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 113])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup70 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions70⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields70 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 33])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 113])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values70 (logical : Nat → F) :
    (sourceExpressions70.map (Verification.environment logical)).toList = sourceFields70 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag70 (logical : Nat → F) :
    ((sourceFields70 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics70 (logical : Nat → F) :
    (sourceLookup70).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields70 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions70.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values70]
    exact source_tag70 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions70 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values70 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values70 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand71 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 49))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 55))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 15⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions71 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 34])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 114])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup71 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions71⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields71 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 34])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 114])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values71 (logical : Nat → F) :
    (sourceExpressions71.map (Verification.environment logical)).toList = sourceFields71 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag71 (logical : Nat → F) :
    ((sourceFields71 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics71 (logical : Nat → F) :
    (sourceLookup71).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields71 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions71.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values71]
    exact source_tag71 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions71 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values71 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values71 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.Bigint
