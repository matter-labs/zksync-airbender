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
noncomputable def operand24 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 65)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 504))], ⟨⟨133099247, by decide⟩⟩⟩, 24⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions24 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 666]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 667])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup24 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions24⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields24 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 666]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 667])])).eval (Verification.environment logical)]

theorem source_values24 (logical : Nat → F) :
    (sourceExpressions24.map (Verification.environment logical)).toList = sourceFields24 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics24 (logical : Nat → F) :
    (sourceLookup24).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields24 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup24, sourceExpressions24, sourceFields24, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 666]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 667])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand25 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 70)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 505))], ⟨⟨1476395013, by decide⟩⟩⟩, 25⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions25 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 668]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 670])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup25 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions25⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields25 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 668]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 670])])).eval (Verification.environment logical)]

theorem source_values25 (logical : Nat → F) :
    (sourceExpressions25.map (Verification.environment logical)).toList = sourceFields25 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics25 (logical : Nat → F) :
    (sourceLookup25).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields25 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup25, sourceExpressions25, sourceFields25, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 668]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 670])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand26 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 71)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 505))], ⟨⟨133099247, by decide⟩⟩⟩, 26⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions26 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 669]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 670])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup26 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions26⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields26 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 669]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 670])])).eval (Verification.environment logical)]

theorem source_values26 (logical : Nat → F) :
    (sourceExpressions26.map (Verification.environment logical)).toList = sourceFields26 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics26 (logical : Nat → F) :
    (sourceLookup26).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields26 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup26, sourceExpressions26, sourceFields26, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 669]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 670])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand27 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 76)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 506))], ⟨⟨1476395013, by decide⟩⟩⟩, 27⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions27 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 671]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 673])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup27 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions27⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields27 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 671]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 673])])).eval (Verification.environment logical)]

theorem source_values27 (logical : Nat → F) :
    (sourceExpressions27.map (Verification.environment logical)).toList = sourceFields27 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics27 (logical : Nat → F) :
    (sourceLookup27).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields27 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup27, sourceExpressions27, sourceFields27, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 671]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 673])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand28 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 77)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 506))], ⟨⟨133099247, by decide⟩⟩⟩, 28⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions28 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 672]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 673])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup28 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions28⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields28 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 672]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 673])])).eval (Verification.environment logical)]

theorem source_values28 (logical : Nat → F) :
    (sourceExpressions28.map (Verification.environment logical)).toList = sourceFields28 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics28 (logical : Nat → F) :
    (sourceLookup28).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields28 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup28, sourceExpressions28, sourceFields28, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 672]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 673])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand29 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 82)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 507))], ⟨⟨1476395013, by decide⟩⟩⟩, 29⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions29 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 674]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 676])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup29 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions29⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields29 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 674]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 676])])).eval (Verification.environment logical)]

theorem source_values29 (logical : Nat → F) :
    (sourceExpressions29.map (Verification.environment logical)).toList = sourceFields29 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics29 (logical : Nat → F) :
    (sourceLookup29).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields29 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup29, sourceExpressions29, sourceFields29, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 674]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 676])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand30 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 83)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 507))], ⟨⟨133099247, by decide⟩⟩⟩, 30⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions30 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 675]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 676])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup30 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions30⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields30 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 675]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 676])])).eval (Verification.environment logical)]

theorem source_values30 (logical : Nat → F) :
    (sourceExpressions30.map (Verification.environment logical)).toList = sourceFields30 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics30 (logical : Nat → F) :
    (sourceLookup30).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields30 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup30, sourceExpressions30, sourceFields30, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 675]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 676])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand31 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 88)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 508))], ⟨⟨1476395013, by decide⟩⟩⟩, 31⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions31 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 677]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 679])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup31 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions31⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields31 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 677]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 679])])).eval (Verification.environment logical)]

theorem source_values31 (logical : Nat → F) :
    (sourceExpressions31.map (Verification.environment logical)).toList = sourceFields31 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics31 (logical : Nat → F) :
    (sourceLookup31).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields31 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup31, sourceExpressions31, sourceFields31, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 677]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 679])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand32 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 89)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 508))], ⟨⟨133099247, by decide⟩⟩⟩, 32⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions32 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 678]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 679])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup32 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions32⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields32 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 678]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 679])])).eval (Verification.environment logical)]

theorem source_values32 (logical : Nat → F) :
    (sourceExpressions32.map (Verification.environment logical)).toList = sourceFields32 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics32 (logical : Nat → F) :
    (sourceLookup32).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields32 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup32, sourceExpressions32, sourceFields32, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 678]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 679])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand33 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 94)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 509))], ⟨⟨1476395013, by decide⟩⟩⟩, 33⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions33 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 680]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 682])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup33 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions33⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields33 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 680]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 682])])).eval (Verification.environment logical)]

theorem source_values33 (logical : Nat → F) :
    (sourceExpressions33.map (Verification.environment logical)).toList = sourceFields33 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics33 (logical : Nat → F) :
    (sourceLookup33).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields33 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup33, sourceExpressions33, sourceFields33, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 680]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 682])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand34 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 95)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 509))], ⟨⟨133099247, by decide⟩⟩⟩, 34⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions34 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 681]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 682])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup34 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions34⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields34 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 681]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 682])])).eval (Verification.environment logical)]

theorem source_values34 (logical : Nat → F) :
    (sourceExpressions34.map (Verification.environment logical)).toList = sourceFields34 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics34 (logical : Nat → F) :
    (sourceLookup34).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields34 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup34, sourceExpressions34, sourceFields34, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 681]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 682])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand35 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 100)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 510))], ⟨⟨1476395013, by decide⟩⟩⟩, 35⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions35 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 683]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 685])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup35 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions35⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields35 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 683]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 685])])).eval (Verification.environment logical)]

theorem source_values35 (logical : Nat → F) :
    (sourceExpressions35.map (Verification.environment logical)).toList = sourceFields35 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics35 (logical : Nat → F) :
    (sourceLookup35).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields35 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup35, sourceExpressions35, sourceFields35, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 683]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 685])])) logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
