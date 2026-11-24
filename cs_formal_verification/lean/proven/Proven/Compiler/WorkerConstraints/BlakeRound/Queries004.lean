module
public import Proven.Compiler.WorkerConstraints.Values
public import Proven.Compiler.WorkerConstraints.Setup
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One actual resolved primitive operand. -/
noncomputable def operand48 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 137)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 516))], ⟨⟨133099247, by decide⟩⟩⟩, 48⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions48 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 702]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 703])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup48 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions48⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields48 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 702]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 703])])).eval (Verification.environment logical)]

theorem source_values48 (logical : Nat → F) :
    (sourceExpressions48.map (Verification.environment logical)).toList = sourceFields48 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics48 (logical : Nat → F) :
    (sourceLookup48).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields48 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup48, sourceExpressions48, sourceFields48, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 702]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 703])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand49 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 142)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 517))], ⟨⟨1476395013, by decide⟩⟩⟩, 49⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions49 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 704]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 706])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup49 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions49⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields49 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 704]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 706])])).eval (Verification.environment logical)]

theorem source_values49 (logical : Nat → F) :
    (sourceExpressions49.map (Verification.environment logical)).toList = sourceFields49 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics49 (logical : Nat → F) :
    (sourceLookup49).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields49 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup49, sourceExpressions49, sourceFields49, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 704]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 706])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand50 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 143)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 517))], ⟨⟨133099247, by decide⟩⟩⟩, 50⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions50 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 705]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 706])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup50 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions50⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields50 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 705]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 706])])).eval (Verification.environment logical)]

theorem source_values50 (logical : Nat → F) :
    (sourceExpressions50.map (Verification.environment logical)).toList = sourceFields50 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics50 (logical : Nat → F) :
    (sourceLookup50).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields50 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup50, sourceExpressions50, sourceFields50, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 705]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 706])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand51 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 148)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 518))], ⟨⟨1476395013, by decide⟩⟩⟩, 51⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions51 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 707]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 709])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup51 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions51⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields51 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 707]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 709])])).eval (Verification.environment logical)]

theorem source_values51 (logical : Nat → F) :
    (sourceExpressions51.map (Verification.environment logical)).toList = sourceFields51 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics51 (logical : Nat → F) :
    (sourceLookup51).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields51 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup51, sourceExpressions51, sourceFields51, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 707]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 709])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand52 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 149)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 518))], ⟨⟨133099247, by decide⟩⟩⟩, 52⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions52 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 708]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 709])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup52 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions52⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields52 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 708]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 709])])).eval (Verification.environment logical)]

theorem source_values52 (logical : Nat → F) :
    (sourceExpressions52.map (Verification.environment logical)).toList = sourceFields52 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics52 (logical : Nat → F) :
    (sourceLookup52).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields52 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup52, sourceExpressions52, sourceFields52, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 708]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 709])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand53 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 152)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 519))], ⟨⟨1476395013, by decide⟩⟩⟩, 53⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions53 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 710]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 712])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup53 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions53⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields53 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 710]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 712])])).eval (Verification.environment logical)]

theorem source_values53 (logical : Nat → F) :
    (sourceExpressions53.map (Verification.environment logical)).toList = sourceFields53 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics53 (logical : Nat → F) :
    (sourceLookup53).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields53 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup53, sourceExpressions53, sourceFields53, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 710]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 712])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand54 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 153)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 519))], ⟨⟨133099247, by decide⟩⟩⟩, 54⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions54 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 711]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 712])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup54 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions54⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields54 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 711]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 712])])).eval (Verification.environment logical)]

theorem source_values54 (logical : Nat → F) :
    (sourceExpressions54.map (Verification.environment logical)).toList = sourceFields54 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics54 (logical : Nat → F) :
    (sourceLookup54).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields54 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup54, sourceExpressions54, sourceFields54, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 711]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 712])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand55 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 156)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 520))], ⟨⟨1476395013, by decide⟩⟩⟩, 55⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions55 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 713]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 715])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup55 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions55⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields55 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 713]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 715])])).eval (Verification.environment logical)]

theorem source_values55 (logical : Nat → F) :
    (sourceExpressions55.map (Verification.environment logical)).toList = sourceFields55 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics55 (logical : Nat → F) :
    (sourceLookup55).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields55 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup55, sourceExpressions55, sourceFields55, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 713]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 715])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand56 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 157)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 520))], ⟨⟨133099247, by decide⟩⟩⟩, 56⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions56 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 714]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 715])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup56 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions56⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields56 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 714]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 715])])).eval (Verification.environment logical)]

theorem source_values56 (logical : Nat → F) :
    (sourceExpressions56.map (Verification.environment logical)).toList = sourceFields56 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics56 (logical : Nat → F) :
    (sourceLookup56).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields56 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup56, sourceExpressions56, sourceFields56, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 714]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 715])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand57 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 160)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 521))], ⟨⟨1476395013, by decide⟩⟩⟩, 57⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions57 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 716]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 718])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup57 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions57⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields57 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 716]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 718])])).eval (Verification.environment logical)]

theorem source_values57 (logical : Nat → F) :
    (sourceExpressions57.map (Verification.environment logical)).toList = sourceFields57 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics57 (logical : Nat → F) :
    (sourceLookup57).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields57 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup57, sourceExpressions57, sourceFields57, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 716]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 718])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand58 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 161)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 521))], ⟨⟨133099247, by decide⟩⟩⟩, 58⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions58 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 717]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 718])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup58 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions58⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields58 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 717]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 718])])).eval (Verification.environment logical)]

theorem source_values58 (logical : Nat → F) :
    (sourceExpressions58.map (Verification.environment logical)).toList = sourceFields58 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics58 (logical : Nat → F) :
    (sourceLookup58).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields58 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup58, sourceExpressions58, sourceFields58, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 717]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 718])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand59 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 164)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 522))], ⟨⟨1476395013, by decide⟩⟩⟩, 59⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions59 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 719]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 721])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup59 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions59⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields59 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 719]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 721])])).eval (Verification.environment logical)]

theorem source_values59 (logical : Nat → F) :
    (sourceExpressions59.map (Verification.environment logical)).toList = sourceFields59 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics59 (logical : Nat → F) :
    (sourceLookup59).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields59 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup59, sourceExpressions59, sourceFields59, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 719]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 721])])) logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
