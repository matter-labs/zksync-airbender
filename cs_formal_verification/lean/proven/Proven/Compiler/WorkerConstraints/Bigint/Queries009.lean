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
noncomputable def operand108 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 86)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 118))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524041, by decide⟩⟩⟩], 52⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions108 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 145]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 177])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup108 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions108⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields108 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 145]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 177])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values108 (logical : Nat → F) :
    (sourceExpressions108.map (Verification.environment logical)).toList = sourceFields108 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag108 (logical : Nat → F) :
    ((sourceFields108 logical)[2]?).getD 0 ≠ 0 := by
  change (26 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics108 (logical : Nat → F) :
    (sourceLookup108).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields108 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions108.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values108]
    exact source_tag108 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions108 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values108 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values108 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand109 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 87)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 119))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524041, by decide⟩⟩⟩], 53⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions109 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 146]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 178])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup109 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions109⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields109 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 146]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 178])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values109 (logical : Nat → F) :
    (sourceExpressions109.map (Verification.environment logical)).toList = sourceFields109 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag109 (logical : Nat → F) :
    ((sourceFields109 logical)[2]?).getD 0 ≠ 0 := by
  change (26 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics109 (logical : Nat → F) :
    (sourceLookup109).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields109 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions109.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values109]
    exact source_tag109 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions109 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values109 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values109 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand110 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 88)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 120))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524041, by decide⟩⟩⟩], 54⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions110 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 147]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 179])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup110 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions110⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields110 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 147]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 179])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values110 (logical : Nat → F) :
    (sourceExpressions110.map (Verification.environment logical)).toList = sourceFields110 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag110 (logical : Nat → F) :
    ((sourceFields110 logical)[2]?).getD 0 ≠ 0 := by
  change (26 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics110 (logical : Nat → F) :
    (sourceLookup110).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields110 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions110.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values110]
    exact source_tag110 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions110 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values110 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values110 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand111 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 89)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 121))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524041, by decide⟩⟩⟩], 55⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions111 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 148]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 180])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup111 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions111⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields111 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 148]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 180])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values111 (logical : Nat → F) :
    (sourceExpressions111.map (Verification.environment logical)).toList = sourceFields111 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag111 (logical : Nat → F) :
    ((sourceFields111 logical)[2]?).getD 0 ≠ 0 := by
  change (26 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics111 (logical : Nat → F) :
    (sourceLookup111).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields111 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions111.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values111]
    exact source_tag111 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions111 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values111 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values111 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand112 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 90)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 122))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524041, by decide⟩⟩⟩], 56⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions112 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 149]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 181])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup112 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions112⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields112 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 149]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 181])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values112 (logical : Nat → F) :
    (sourceExpressions112.map (Verification.environment logical)).toList = sourceFields112 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag112 (logical : Nat → F) :
    ((sourceFields112 logical)[2]?).getD 0 ≠ 0 := by
  change (26 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics112 (logical : Nat → F) :
    (sourceLookup112).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields112 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions112.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values112]
    exact source_tag112 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions112 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values112 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values112 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand113 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 91)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 123))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524041, by decide⟩⟩⟩], 57⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions113 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 150]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 182])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup113 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions113⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields113 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 150]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 182])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values113 (logical : Nat → F) :
    (sourceExpressions113.map (Verification.environment logical)).toList = sourceFields113 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag113 (logical : Nat → F) :
    ((sourceFields113 logical)[2]?).getD 0 ≠ 0 := by
  change (26 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics113 (logical : Nat → F) :
    (sourceLookup113).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields113 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions113.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values113]
    exact source_tag113 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions113 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values113 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values113 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand114 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 92)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 124))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524041, by decide⟩⟩⟩], 58⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions114 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 151]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 183])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup114 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions114⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields114 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 151]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 183])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values114 (logical : Nat → F) :
    (sourceExpressions114.map (Verification.environment logical)).toList = sourceFields114 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag114 (logical : Nat → F) :
    ((sourceFields114 logical)[2]?).getD 0 ≠ 0 := by
  change (26 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics114 (logical : Nat → F) :
    (sourceLookup114).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields114 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions114.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values114]
    exact source_tag114 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions114 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values114 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values114 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand115 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 93)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 125))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524041, by decide⟩⟩⟩], 59⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions115 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 152]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 184])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup115 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions115⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields115 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 152]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 184])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values115 (logical : Nat → F) :
    (sourceExpressions115.map (Verification.environment logical)).toList = sourceFields115 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag115 (logical : Nat → F) :
    ((sourceFields115 logical)[2]?).getD 0 ≠ 0 := by
  change (26 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics115 (logical : Nat → F) :
    (sourceLookup115).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields115 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions115.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values115]
    exact source_tag115 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions115 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values115 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values115 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand116 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 94)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 126))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524041, by decide⟩⟩⟩], 60⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions116 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 153]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 185])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup116 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions116⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields116 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 153]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 185])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524041, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values116 (logical : Nat → F) :
    (sourceExpressions116.map (Verification.environment logical)).toList = sourceFields116 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag116 (logical : Nat → F) :
    ((sourceFields116 logical)[2]?).getD 0 ≠ 0 := by
  change (26 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics116 (logical : Nat → F) :
    (sourceLookup116).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields116 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions116.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values116]
    exact source_tag116 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions116 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values116 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values116 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand117 : NativeLookups.Operand := ⟨.one, .address (.InnerLayer 1 21)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions117 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 194])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup117 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions117⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields117 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 194])])).eval (Verification.environment logical)]

theorem source_values117 (logical : Nat → F) :
    (sourceExpressions117.map (Verification.environment logical)).toList = sourceFields117 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics117 (logical : Nat → F) :
    (sourceLookup117).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields117 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup117, sourceExpressions117, sourceFields117, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 194])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand118 : NativeLookups.Operand := ⟨.one, .address (.InnerLayer 1 22)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions118 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 195])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup118 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions118⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields118 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 195])])).eval (Verification.environment logical)]

theorem source_values118 (logical : Nat → F) :
    (sourceExpressions118.map (Verification.environment logical)).toList = sourceFields118 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics118 (logical : Nat → F) :
    (sourceLookup118).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields118 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup118, sourceExpressions118, sourceFields118, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 195])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand119 : NativeLookups.Operand := ⟨.one, .address (.InnerLayer 1 23)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions119 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 196])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup119 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions119⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields119 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 196])])).eval (Verification.environment logical)]

theorem source_values119 (logical : Nat → F) :
    (sourceExpressions119.map (Verification.environment logical)).toList = sourceFields119 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics119 (logical : Nat → F) :
    (sourceLookup119).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields119 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup119, sourceExpressions119, sourceFields119, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 196])])) logical


end Airbender.Compiler.WorkerConstraints.Bigint
