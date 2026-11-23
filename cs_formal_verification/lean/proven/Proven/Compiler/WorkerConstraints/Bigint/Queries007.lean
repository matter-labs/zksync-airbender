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
noncomputable def operand84 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 82))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 68))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 28⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions84 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 51])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 127])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup84 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions84⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields84 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 51])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 127])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values84 (logical : Nat → F) :
    (sourceExpressions84.map (Verification.environment logical)).toList = sourceFields84 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag84 (logical : Nat → F) :
    ((sourceFields84 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics84 (logical : Nat → F) :
    (sourceLookup84).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields84 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions84.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values84]
    exact source_tag84 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions84 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values84 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values84 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand85 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 83))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 69))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 29⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions85 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 52])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 128])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup85 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions85⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields85 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 52])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 128])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values85 (logical : Nat → F) :
    (sourceExpressions85.map (Verification.environment logical)).toList = sourceFields85 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag85 (logical : Nat → F) :
    ((sourceFields85 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics85 (logical : Nat → F) :
    (sourceLookup85).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields85 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions85.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values85]
    exact source_tag85 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions85 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values85 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values85 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand86 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 86))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 70))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 30⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions86 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 53])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 129])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup86 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions86⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields86 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 53])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 129])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values86 (logical : Nat → F) :
    (sourceExpressions86.map (Verification.environment logical)).toList = sourceFields86 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag86 (logical : Nat → F) :
    ((sourceFields86 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics86 (logical : Nat → F) :
    (sourceLookup86).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields86 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions86.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values86]
    exact source_tag86 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions86 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values86 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values86 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand87 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 87))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 71))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 31⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions87 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 54])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 130])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup87 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions87⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields87 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 54])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 130])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values87 (logical : Nat → F) :
    (sourceExpressions87.map (Verification.environment logical)).toList = sourceFields87 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag87 (logical : Nat → F) :
    ((sourceFields87 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics87 (logical : Nat → F) :
    (sourceLookup87).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields87 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions87.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values87]
    exact source_tag87 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions87 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values87 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values87 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand88 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 72)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 104))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 102)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 134))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1879048146, by decide⟩⟩⟩], 32⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions88 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 131]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 163])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 161]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 193])]), Import.expression (.Sum #[(.Constant ⟨⟨1879048146, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup88 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions88⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields88 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 131]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 163])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 161]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 193])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1879048146, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values88 (logical : Nat → F) :
    (sourceExpressions88.map (Verification.environment logical)).toList = sourceFields88 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag88 (logical : Nat → F) :
    ((sourceFields88 logical)[2]?).getD 0 ≠ 0 := by
  change (22 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics88 (logical : Nat → F) :
    (sourceLookup88).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields88 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions88.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values88]
    exact source_tag88 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions88 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values88 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values88 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand89 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 73)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 105))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 101)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 133))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨134217679, by decide⟩⟩⟩], 33⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions89 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 132]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 164])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 160]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 192])]), Import.expression (.Sum #[(.Constant ⟨⟨134217679, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup89 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions89⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields89 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 132]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 164])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 160]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 192])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨134217679, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values89 (logical : Nat → F) :
    (sourceExpressions89.map (Verification.environment logical)).toList = sourceFields89 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag89 (logical : Nat → F) :
    ((sourceFields89 logical)[2]?).getD 0 ≠ 0 := by
  change (23 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics89 (logical : Nat → F) :
    (sourceLookup89).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields89 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions89.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values89]
    exact source_tag89 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions89 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values89 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values89 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand90 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 74)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 106))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨402653133, by decide⟩⟩⟩], 34⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions90 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 133]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 165])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨402653133, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup90 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions90⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields90 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 133]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 165])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨402653133, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values90 (logical : Nat → F) :
    (sourceExpressions90.map (Verification.environment logical)).toList = sourceFields90 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag90 (logical : Nat → F) :
    ((sourceFields90 logical)[2]?).getD 0 ≠ 0 := by
  change (24 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics90 (logical : Nat → F) :
    (sourceLookup90).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields90 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions90.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values90]
    exact source_tag90 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions90 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values90 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values90 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand91 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 75)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 107))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨402653133, by decide⟩⟩⟩], 35⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions91 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 134]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 166])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨402653133, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup91 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions91⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields91 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 134]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 166])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨402653133, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values91 (logical : Nat → F) :
    (sourceExpressions91.map (Verification.environment logical)).toList = sourceFields91 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag91 (logical : Nat → F) :
    ((sourceFields91 logical)[2]?).getD 0 ≠ 0 := by
  change (24 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics91 (logical : Nat → F) :
    (sourceLookup91).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields91 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions91.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values91]
    exact source_tag91 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions91 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values91 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values91 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand92 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 99)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 131))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨402653133, by decide⟩⟩⟩], 36⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions92 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 158]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 190])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨402653133, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup92 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions92⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields92 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 158]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 190])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨402653133, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values92 (logical : Nat → F) :
    (sourceExpressions92.map (Verification.environment logical)).toList = sourceFields92 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag92 (logical : Nat → F) :
    ((sourceFields92 logical)[2]?).getD 0 ≠ 0 := by
  change (24 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics92 (logical : Nat → F) :
    (sourceLookup92).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields92 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions92.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values92]
    exact source_tag92 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions92 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values92 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values92 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand93 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 100)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 132))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨402653133, by decide⟩⟩⟩], 37⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions93 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 159]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 191])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨402653133, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup93 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions93⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields93 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 159]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 191])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨402653133, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values93 (logical : Nat → F) :
    (sourceExpressions93.map (Verification.environment logical)).toList = sourceFields93 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag93 (logical : Nat → F) :
    ((sourceFields93 logical)[2]?).getD 0 ≠ 0 := by
  change (24 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics93 (logical : Nat → F) :
    (sourceLookup93).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields93 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions93.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values93]
    exact source_tag93 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions93 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values93 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values93 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand94 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 76)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 108))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088587, by decide⟩⟩⟩], 38⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions94 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 135]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 167])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088587, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup94 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions94⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields94 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 135]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 167])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088587, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values94 (logical : Nat → F) :
    (sourceExpressions94.map (Verification.environment logical)).toList = sourceFields94 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag94 (logical : Nat → F) :
    ((sourceFields94 logical)[2]?).getD 0 ≠ 0 := by
  change (25 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics94 (logical : Nat → F) :
    (sourceLookup94).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields94 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions94.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values94]
    exact source_tag94 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions94 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values94 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values94 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand95 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerWitness 77)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 109))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088587, by decide⟩⟩⟩], 39⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions95 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 136]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 168])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088587, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup95 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions95⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields95 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 136]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 168])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088587, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values95 (logical : Nat → F) :
    (sourceExpressions95.map (Verification.environment logical)).toList = sourceFields95 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag95 (logical : Nat → F) :
    ((sourceFields95 logical)[2]?).getD 0 ≠ 0 := by
  change (25 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics95 (logical : Nat → F) :
    (sourceLookup95).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields95 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions95.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values95]
    exact source_tag95 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions95 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values95 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values95 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.Bigint
