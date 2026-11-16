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
noncomputable def operand24 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 95)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 22)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 142))], ⟨⟨1476395013, by decide⟩⟩⟩, 9⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions24 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 228]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 230])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup24 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions24⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields24 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 228]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 230])])).eval (Verification.environment logical)]

theorem source_values24 (logical : Nat → F) :
    (sourceExpressions24.map (Verification.environment logical)).toList = sourceFields24 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics24 (logical : Nat → F) :
    (sourceLookup24).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields24 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup24, sourceExpressions24, sourceFields24, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 228]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 230])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand25 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 96)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 23)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 142))], ⟨⟨133099247, by decide⟩⟩⟩, 10⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions25 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 229]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 230])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup25 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions25⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields25 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 229]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 230])])).eval (Verification.environment logical)]

theorem source_values25 (logical : Nat → F) :
    (sourceExpressions25.map (Verification.environment logical)).toList = sourceFields25 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics25 (logical : Nat → F) :
    (sourceLookup25).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields25 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup25, sourceExpressions25, sourceFields25, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 229]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 230])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand26 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 95)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 28)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 143))], ⟨⟨1476395013, by decide⟩⟩⟩, 11⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions26 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 231]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 233])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup26 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions26⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields26 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 231]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 233])])).eval (Verification.environment logical)]

theorem source_values26 (logical : Nat → F) :
    (sourceExpressions26.map (Verification.environment logical)).toList = sourceFields26 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics26 (logical : Nat → F) :
    (sourceLookup26).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields26 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup26, sourceExpressions26, sourceFields26, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 231]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 233])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand27 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 96)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 29)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 143))], ⟨⟨133099247, by decide⟩⟩⟩, 12⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions27 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 232]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 233])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup27 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions27⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields27 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 232]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 233])])).eval (Verification.environment logical)]

theorem source_values27 (logical : Nat → F) :
    (sourceExpressions27.map (Verification.environment logical)).toList = sourceFields27 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics27 (logical : Nat → F) :
    (sourceLookup27).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields27 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup27, sourceExpressions27, sourceFields27, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 232]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 233])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand28 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 95)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 34)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 144))], ⟨⟨1476395013, by decide⟩⟩⟩, 13⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions28 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 234]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 236])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup28 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions28⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields28 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 234]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 236])])).eval (Verification.environment logical)]

theorem source_values28 (logical : Nat → F) :
    (sourceExpressions28.map (Verification.environment logical)).toList = sourceFields28 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics28 (logical : Nat → F) :
    (sourceLookup28).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields28 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup28, sourceExpressions28, sourceFields28, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 234]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 236])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand29 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 96)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 35)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 144))], ⟨⟨133099247, by decide⟩⟩⟩, 14⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions29 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 235]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 236])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup29 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions29⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields29 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 235]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 236])])).eval (Verification.environment logical)]

theorem source_values29 (logical : Nat → F) :
    (sourceExpressions29.map (Verification.environment logical)).toList = sourceFields29 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics29 (logical : Nat → F) :
    (sourceLookup29).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields29 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup29, sourceExpressions29, sourceFields29, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 235]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 236])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand30 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 95)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 40)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 145))], ⟨⟨1476395013, by decide⟩⟩⟩, 15⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions30 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 237]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 239])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup30 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions30⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields30 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 237]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 239])])).eval (Verification.environment logical)]

theorem source_values30 (logical : Nat → F) :
    (sourceExpressions30.map (Verification.environment logical)).toList = sourceFields30 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics30 (logical : Nat → F) :
    (sourceLookup30).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields30 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup30, sourceExpressions30, sourceFields30, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 237]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 239])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand31 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 96)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 41)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 145))], ⟨⟨133099247, by decide⟩⟩⟩, 16⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions31 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 238]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 239])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup31 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions31⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields31 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 238]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 239])])).eval (Verification.environment logical)]

theorem source_values31 (logical : Nat → F) :
    (sourceExpressions31.map (Verification.environment logical)).toList = sourceFields31 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics31 (logical : Nat → F) :
    (sourceLookup31).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields31 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup31, sourceExpressions31, sourceFields31, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 238]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 239])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand32 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 95)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 46)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 146))], ⟨⟨1476395013, by decide⟩⟩⟩, 17⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions32 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 240]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 242])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup32 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions32⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields32 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 240]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 242])])).eval (Verification.environment logical)]

theorem source_values32 (logical : Nat → F) :
    (sourceExpressions32.map (Verification.environment logical)).toList = sourceFields32 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics32 (logical : Nat → F) :
    (sourceLookup32).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields32 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup32, sourceExpressions32, sourceFields32, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 240]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 242])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand33 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 96)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 47)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 146))], ⟨⟨133099247, by decide⟩⟩⟩, 18⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions33 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 241]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 242])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup33 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions33⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields33 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 241]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 242])])).eval (Verification.environment logical)]

theorem source_values33 (logical : Nat → F) :
    (sourceExpressions33.map (Verification.environment logical)).toList = sourceFields33 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics33 (logical : Nat → F) :
    (sourceLookup33).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields33 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup33, sourceExpressions33, sourceFields33, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 241]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 242])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand34 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 95)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 52)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 147))], ⟨⟨1476395013, by decide⟩⟩⟩, 19⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions34 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 243]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 245])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup34 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions34⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields34 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 243]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 245])])).eval (Verification.environment logical)]

theorem source_values34 (logical : Nat → F) :
    (sourceExpressions34.map (Verification.environment logical)).toList = sourceFields34 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics34 (logical : Nat → F) :
    (sourceLookup34).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields34 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup34, sourceExpressions34, sourceFields34, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 243]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 245])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand35 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 96)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 53)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 147))], ⟨⟨133099247, by decide⟩⟩⟩, 20⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions35 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 244]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 245])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup35 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions35⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields35 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 244]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 245])])).eval (Verification.environment logical)]

theorem source_values35 (logical : Nat → F) :
    (sourceExpressions35.map (Verification.environment logical)).toList = sourceFields35 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics35 (logical : Nat → F) :
    (sourceLookup35).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields35 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup35, sourceExpressions35, sourceFields35, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 244]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 245])])) logical


end Airbender.Compiler.WorkerConstraints.Bigint
