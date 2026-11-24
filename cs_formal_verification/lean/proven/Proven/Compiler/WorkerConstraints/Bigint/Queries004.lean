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
noncomputable def operand48 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 95)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 80)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 154))], ⟨⟨1476395013, by decide⟩⟩⟩, 33⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions48 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 264]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 266])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup48 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions48⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields48 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 264]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 266])])).eval (Verification.environment logical)]

theorem source_values48 (logical : Nat → F) :
    (sourceExpressions48.map (Verification.environment logical)).toList = sourceFields48 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics48 (logical : Nat → F) :
    (sourceLookup48).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields48 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup48, sourceExpressions48, sourceFields48, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 264]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 266])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand49 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 96)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 81)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 154))], ⟨⟨133099247, by decide⟩⟩⟩, 34⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions49 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 265]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 266])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup49 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions49⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields49 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 265]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 266])])).eval (Verification.environment logical)]

theorem source_values49 (logical : Nat → F) :
    (sourceExpressions49.map (Verification.environment logical)).toList = sourceFields49 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics49 (logical : Nat → F) :
    (sourceLookup49).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields49 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup49, sourceExpressions49, sourceFields49, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 265]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 266])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand50 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 95)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 84)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 155))], ⟨⟨1476395013, by decide⟩⟩⟩, 35⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions50 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 267]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 269])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup50 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions50⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields50 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 267]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 269])])).eval (Verification.environment logical)]

theorem source_values50 (logical : Nat → F) :
    (sourceExpressions50.map (Verification.environment logical)).toList = sourceFields50 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics50 (logical : Nat → F) :
    (sourceLookup50).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields50 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup50, sourceExpressions50, sourceFields50, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 267]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 269])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand51 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 96)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 85)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 155))], ⟨⟨133099247, by decide⟩⟩⟩, 36⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions51 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 268]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 269])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup51 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions51⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields51 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 268]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 269])])).eval (Verification.environment logical)]

theorem source_values51 (logical : Nat → F) :
    (sourceExpressions51.map (Verification.environment logical)).toList = sourceFields51 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics51 (logical : Nat → F) :
    (sourceLookup51).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields51 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup51, sourceExpressions51, sourceFields51, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 268]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 269])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand52 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 95)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 88)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 156))], ⟨⟨1476395013, by decide⟩⟩⟩, 37⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions52 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 270]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 272])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup52 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions52⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields52 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 270]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 272])])).eval (Verification.environment logical)]

theorem source_values52 (logical : Nat → F) :
    (sourceExpressions52.map (Verification.environment logical)).toList = sourceFields52 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics52 (logical : Nat → F) :
    (sourceLookup52).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields52 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup52, sourceExpressions52, sourceFields52, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 270]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 272])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand53 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 96)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 89)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 156))], ⟨⟨133099247, by decide⟩⟩⟩, 38⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions53 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 271]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 272])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup53 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions53⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields53 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 271]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 272])])).eval (Verification.environment logical)]

theorem source_values53 (logical : Nat → F) :
    (sourceExpressions53.map (Verification.environment logical)).toList = sourceFields53 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics53 (logical : Nat → F) :
    (sourceLookup53).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields53 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup53, sourceExpressions53, sourceFields53, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 271]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 272])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand54 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨134217728, by decide⟩⟩, (.BaseLayerMemory 2))], ⟨⟨0, by decide⟩⟩⟩, 39⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions54 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨134217728, by decide⟩⟩, .Var 3])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup54 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions54⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields54 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨134217728, by decide⟩⟩, .Var 3])])).eval (Verification.environment logical)]

theorem source_values54 (logical : Nat → F) :
    (sourceExpressions54.map (Verification.environment logical)).toList = sourceFields54 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics54 (logical : Nat → F) :
    (sourceLookup54).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields54 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup54, sourceExpressions54, sourceFields54, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨134217728, by decide⟩⟩, .Var 3])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand55 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨134217728, by decide⟩⟩, (.BaseLayerMemory 54))], ⟨⟨0, by decide⟩⟩⟩, 40⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions55 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨134217728, by decide⟩⟩, .Var 37])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup55 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions55⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields55 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨134217728, by decide⟩⟩, .Var 37])])).eval (Verification.environment logical)]

theorem source_values55 (logical : Nat → F) :
    (sourceExpressions55.map (Verification.environment logical)).toList = sourceFields55 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics55 (logical : Nat → F) :
    (sourceLookup55).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields55 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup55, sourceExpressions55, sourceFields55, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨134217728, by decide⟩⟩, .Var 37])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand56 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 6))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 40))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 0⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions56 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 5])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 99])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup56 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions56⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields56 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 5])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 99])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values56 (logical : Nat → F) :
    (sourceExpressions56.map (Verification.environment logical)).toList = sourceFields56 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag56 (logical : Nat → F) :
    ((sourceFields56 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics56 (logical : Nat → F) :
    (sourceLookup56).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields56 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions56.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values56]
    exact source_tag56 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions56 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values56 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values56 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand57 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 7))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 41))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 1⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions57 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 6])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 100])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup57 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions57⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields57 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 6])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 100])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values57 (logical : Nat → F) :
    (sourceExpressions57.map (Verification.environment logical)).toList = sourceFields57 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag57 (logical : Nat → F) :
    ((sourceFields57 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics57 (logical : Nat → F) :
    (sourceLookup57).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields57 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions57.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values57]
    exact source_tag57 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions57 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values57 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values57 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand58 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 12))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 42))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 2⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions58 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 9])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 101])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup58 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions58⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields58 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 9])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 101])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values58 (logical : Nat → F) :
    (sourceExpressions58.map (Verification.environment logical)).toList = sourceFields58 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag58 (logical : Nat → F) :
    ((sourceFields58 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics58 (logical : Nat → F) :
    (sourceLookup58).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields58 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions58.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values58]
    exact source_tag58 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions58 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values58 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values58 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand59 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 13))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 43))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939524009, by decide⟩⟩⟩], 3⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions59 : Vector (Airbender.Expression F) 3 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 10])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 102])]), Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup59 : Lookup F := ⟨(WorkerConstraints.setupTable .bigint).toRaw, sourceExpressions59⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields59 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 10])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 102])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939524009, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values59 (logical : Nat → F) :
    (sourceExpressions59.map (Verification.environment logical)).toList = sourceFields59 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag59 (logical : Nat → F) :
    ((sourceFields59 logical)[2]?).getD 0 ≠ 0 := by
  change (41 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics59 (logical : Nat → F) :
    (sourceLookup59).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields59 logical = NativeWorkerSetup.rows .bigint 0 index := by
  have tag : (((sourceExpressions59.map (Verification.environment logical)).toList)[width .bigint - 1]?).getD 0 ≠ 0 := by
    rw [source_values59]
    exact source_tag59 logical
  have equivalent := generic_lookup_refinement .bigint sourceExpressions59 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values59 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values59 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.Bigint
