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
noncomputable def operand0 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1073741824, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨939524097, by decide⟩⟩, (.BaseLayerMemory 222))], ⟨⟨0, by decide⟩⟩⟩, 0⟩⟩

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
      ∃ index, sourceFields0 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup0, sourceExpressions0, sourceFields0, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741824, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨939524097, by decide⟩⟩, .Var 0])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand1 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 0)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 493))], ⟨⟨1476395013, by decide⟩⟩⟩, 1⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions1 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 632]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 634])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup1 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions1⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields1 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 632]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 634])])).eval (Verification.environment logical)]

theorem source_values1 (logical : Nat → F) :
    (sourceExpressions1.map (Verification.environment logical)).toList = sourceFields1 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics1 (logical : Nat → F) :
    (sourceLookup1).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields1 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup1, sourceExpressions1, sourceFields1, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 632]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 634])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand2 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 1)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 493))], ⟨⟨133099247, by decide⟩⟩⟩, 2⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions2 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 633]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 634])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup2 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions2⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields2 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 633]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 634])])).eval (Verification.environment logical)]

theorem source_values2 (logical : Nat → F) :
    (sourceExpressions2.map (Verification.environment logical)).toList = sourceFields2 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics2 (logical : Nat → F) :
    (sourceLookup2).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields2 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup2, sourceExpressions2, sourceFields2, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 633]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 634])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand3 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 4)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 494))], ⟨⟨1476395013, by decide⟩⟩⟩, 3⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions3 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 635]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 637])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup3 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions3⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields3 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 635]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 637])])).eval (Verification.environment logical)]

theorem source_values3 (logical : Nat → F) :
    (sourceExpressions3.map (Verification.environment logical)).toList = sourceFields3 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics3 (logical : Nat → F) :
    (sourceLookup3).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields3 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup3, sourceExpressions3, sourceFields3, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 635]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 637])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand4 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 5)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 494))], ⟨⟨133099247, by decide⟩⟩⟩, 4⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions4 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 636]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 637])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup4 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions4⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields4 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 636]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 637])])).eval (Verification.environment logical)]

theorem source_values4 (logical : Nat → F) :
    (sourceExpressions4.map (Verification.environment logical)).toList = sourceFields4 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics4 (logical : Nat → F) :
    (sourceLookup4).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields4 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup4, sourceExpressions4, sourceFields4, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 636]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 637])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand5 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 10)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 495))], ⟨⟨1476395013, by decide⟩⟩⟩, 5⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions5 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 638]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 640])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup5 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions5⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields5 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 638]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 640])])).eval (Verification.environment logical)]

theorem source_values5 (logical : Nat → F) :
    (sourceExpressions5.map (Verification.environment logical)).toList = sourceFields5 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics5 (logical : Nat → F) :
    (sourceLookup5).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields5 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup5, sourceExpressions5, sourceFields5, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 638]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 640])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand6 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 11)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 495))], ⟨⟨133099247, by decide⟩⟩⟩, 6⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions6 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 639]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 640])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup6 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions6⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields6 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 639]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 640])])).eval (Verification.environment logical)]

theorem source_values6 (logical : Nat → F) :
    (sourceExpressions6.map (Verification.environment logical)).toList = sourceFields6 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics6 (logical : Nat → F) :
    (sourceLookup6).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields6 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup6, sourceExpressions6, sourceFields6, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 639]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 640])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand7 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 16)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 496))], ⟨⟨1476395013, by decide⟩⟩⟩, 7⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions7 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 641]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 643])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup7 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions7⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields7 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 641]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 643])])).eval (Verification.environment logical)]

theorem source_values7 (logical : Nat → F) :
    (sourceExpressions7.map (Verification.environment logical)).toList = sourceFields7 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics7 (logical : Nat → F) :
    (sourceLookup7).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields7 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup7, sourceExpressions7, sourceFields7, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 641]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 643])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand8 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 17)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 496))], ⟨⟨133099247, by decide⟩⟩⟩, 8⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions8 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 642]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 643])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup8 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions8⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields8 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 642]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 643])])).eval (Verification.environment logical)]

theorem source_values8 (logical : Nat → F) :
    (sourceExpressions8.map (Verification.environment logical)).toList = sourceFields8 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics8 (logical : Nat → F) :
    (sourceLookup8).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields8 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup8, sourceExpressions8, sourceFields8, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 642]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 643])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand9 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 22)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 497))], ⟨⟨1476395013, by decide⟩⟩⟩, 9⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions9 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 644]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 646])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup9 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions9⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields9 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 644]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 646])])).eval (Verification.environment logical)]

theorem source_values9 (logical : Nat → F) :
    (sourceExpressions9.map (Verification.environment logical)).toList = sourceFields9 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics9 (logical : Nat → F) :
    (sourceLookup9).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields9 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup9, sourceExpressions9, sourceFields9, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 644]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 646])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand10 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 23)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 497))], ⟨⟨133099247, by decide⟩⟩⟩, 10⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions10 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 645]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 646])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup10 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions10⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields10 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 645]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 646])])).eval (Verification.environment logical)]

theorem source_values10 (logical : Nat → F) :
    (sourceExpressions10.map (Verification.environment logical)).toList = sourceFields10 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics10 (logical : Nat → F) :
    (sourceLookup10).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields10 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup10, sourceExpressions10, sourceFields10, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 645]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 646])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand11 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 28)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 498))], ⟨⟨1476395013, by decide⟩⟩⟩, 11⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions11 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 647]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 649])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup11 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions11⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields11 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 647]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 649])])).eval (Verification.environment logical)]

theorem source_values11 (logical : Nat → F) :
    (sourceExpressions11.map (Verification.environment logical)).toList = sourceFields11 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics11 (logical : Nat → F) :
    (sourceLookup11).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields11 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup11, sourceExpressions11, sourceFields11, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 647]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 649])])) logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
