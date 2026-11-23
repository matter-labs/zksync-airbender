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
noncomputable def operand60 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 165)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 522))], ⟨⟨133099247, by decide⟩⟩⟩, 60⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions60 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 720]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 721])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup60 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions60⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields60 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 720]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 721])])).eval (Verification.environment logical)]

theorem source_values60 (logical : Nat → F) :
    (sourceExpressions60.map (Verification.environment logical)).toList = sourceFields60 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics60 (logical : Nat → F) :
    (sourceLookup60).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields60 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup60, sourceExpressions60, sourceFields60, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 720]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 721])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand61 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 168)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 523))], ⟨⟨1476395013, by decide⟩⟩⟩, 61⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions61 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 722]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 724])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup61 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions61⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields61 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 722]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 724])])).eval (Verification.environment logical)]

theorem source_values61 (logical : Nat → F) :
    (sourceExpressions61.map (Verification.environment logical)).toList = sourceFields61 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics61 (logical : Nat → F) :
    (sourceLookup61).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields61 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup61, sourceExpressions61, sourceFields61, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 722]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 724])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand62 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 169)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 523))], ⟨⟨133099247, by decide⟩⟩⟩, 62⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions62 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 723]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 724])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup62 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions62⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields62 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 723]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 724])])).eval (Verification.environment logical)]

theorem source_values62 (logical : Nat → F) :
    (sourceExpressions62.map (Verification.environment logical)).toList = sourceFields62 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics62 (logical : Nat → F) :
    (sourceLookup62).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields62 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup62, sourceExpressions62, sourceFields62, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 723]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 724])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand63 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 172)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 524))], ⟨⟨1476395013, by decide⟩⟩⟩, 63⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions63 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 725]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 727])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup63 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions63⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields63 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 725]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 727])])).eval (Verification.environment logical)]

theorem source_values63 (logical : Nat → F) :
    (sourceExpressions63.map (Verification.environment logical)).toList = sourceFields63 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics63 (logical : Nat → F) :
    (sourceLookup63).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields63 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup63, sourceExpressions63, sourceFields63, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 725]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 727])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand64 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 173)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 524))], ⟨⟨133099247, by decide⟩⟩⟩, 64⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions64 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 726]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 727])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup64 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions64⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields64 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 726]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 727])])).eval (Verification.environment logical)]

theorem source_values64 (logical : Nat → F) :
    (sourceExpressions64.map (Verification.environment logical)).toList = sourceFields64 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics64 (logical : Nat → F) :
    (sourceLookup64).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields64 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup64, sourceExpressions64, sourceFields64, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 726]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 727])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand65 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 176)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 525))], ⟨⟨1476395013, by decide⟩⟩⟩, 65⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions65 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 728]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 730])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup65 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions65⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields65 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 728]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 730])])).eval (Verification.environment logical)]

theorem source_values65 (logical : Nat → F) :
    (sourceExpressions65.map (Verification.environment logical)).toList = sourceFields65 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics65 (logical : Nat → F) :
    (sourceLookup65).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields65 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup65, sourceExpressions65, sourceFields65, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 728]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 730])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand66 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 177)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 525))], ⟨⟨133099247, by decide⟩⟩⟩, 66⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions66 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 729]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 730])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup66 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions66⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields66 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 729]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 730])])).eval (Verification.environment logical)]

theorem source_values66 (logical : Nat → F) :
    (sourceExpressions66.map (Verification.environment logical)).toList = sourceFields66 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics66 (logical : Nat → F) :
    (sourceLookup66).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields66 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup66, sourceExpressions66, sourceFields66, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 729]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 730])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand67 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 180)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 526))], ⟨⟨1476395013, by decide⟩⟩⟩, 67⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions67 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 731]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 733])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup67 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions67⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields67 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 731]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 733])])).eval (Verification.environment logical)]

theorem source_values67 (logical : Nat → F) :
    (sourceExpressions67.map (Verification.environment logical)).toList = sourceFields67 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics67 (logical : Nat → F) :
    (sourceLookup67).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields67 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup67, sourceExpressions67, sourceFields67, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 731]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 733])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand68 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 181)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 526))], ⟨⟨133099247, by decide⟩⟩⟩, 68⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions68 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 732]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 733])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup68 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions68⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields68 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 732]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 733])])).eval (Verification.environment logical)]

theorem source_values68 (logical : Nat → F) :
    (sourceExpressions68.map (Verification.environment logical)).toList = sourceFields68 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics68 (logical : Nat → F) :
    (sourceLookup68).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields68 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup68, sourceExpressions68, sourceFields68, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 732]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 733])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand69 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 184)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 527))], ⟨⟨1476395013, by decide⟩⟩⟩, 69⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions69 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 734]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 736])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup69 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions69⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields69 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 734]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 736])])).eval (Verification.environment logical)]

theorem source_values69 (logical : Nat → F) :
    (sourceExpressions69.map (Verification.environment logical)).toList = sourceFields69 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics69 (logical : Nat → F) :
    (sourceLookup69).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields69 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup69, sourceExpressions69, sourceFields69, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 734]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 736])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand70 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 185)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 527))], ⟨⟨133099247, by decide⟩⟩⟩, 70⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions70 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 735]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 736])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup70 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions70⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields70 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 735]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 736])])).eval (Verification.environment logical)]

theorem source_values70 (logical : Nat → F) :
    (sourceExpressions70.map (Verification.environment logical)).toList = sourceFields70 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics70 (logical : Nat → F) :
    (sourceLookup70).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields70 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup70, sourceExpressions70, sourceFields70, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 735]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 736])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand71 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 188)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 528))], ⟨⟨1476395013, by decide⟩⟩⟩, 71⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions71 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 737]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 739])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup71 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions71⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields71 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 737]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 739])])).eval (Verification.environment logical)]

theorem source_values71 (logical : Nat → F) :
    (sourceExpressions71.map (Verification.environment logical)).toList = sourceFields71 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics71 (logical : Nat → F) :
    (sourceLookup71).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields71 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup71, sourceExpressions71, sourceFields71, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 737]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 739])])) logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
