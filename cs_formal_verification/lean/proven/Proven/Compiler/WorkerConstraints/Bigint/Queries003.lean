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
noncomputable def operand36 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 95)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 56)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 148))], ⟨⟨1476395013, by decide⟩⟩⟩, 21⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions36 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 246]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 248])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup36 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions36⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields36 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 246]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 248])])).eval (Verification.environment logical)]

theorem source_values36 (logical : Nat → F) :
    (sourceExpressions36.map (Verification.environment logical)).toList = sourceFields36 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics36 (logical : Nat → F) :
    (sourceLookup36).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields36 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup36, sourceExpressions36, sourceFields36, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 246]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 248])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand37 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 96)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 57)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 148))], ⟨⟨133099247, by decide⟩⟩⟩, 22⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions37 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 247]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 248])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup37 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions37⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields37 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 247]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 248])])).eval (Verification.environment logical)]

theorem source_values37 (logical : Nat → F) :
    (sourceExpressions37.map (Verification.environment logical)).toList = sourceFields37 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics37 (logical : Nat → F) :
    (sourceLookup37).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields37 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup37, sourceExpressions37, sourceFields37, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 247]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 248])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand38 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 95)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 60)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 149))], ⟨⟨1476395013, by decide⟩⟩⟩, 23⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions38 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 249]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 251])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup38 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions38⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields38 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 249]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 251])])).eval (Verification.environment logical)]

theorem source_values38 (logical : Nat → F) :
    (sourceExpressions38.map (Verification.environment logical)).toList = sourceFields38 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics38 (logical : Nat → F) :
    (sourceLookup38).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields38 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup38, sourceExpressions38, sourceFields38, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 249]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 251])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand39 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 96)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 61)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 149))], ⟨⟨133099247, by decide⟩⟩⟩, 24⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions39 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 250]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 251])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup39 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions39⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields39 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 250]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 251])])).eval (Verification.environment logical)]

theorem source_values39 (logical : Nat → F) :
    (sourceExpressions39.map (Verification.environment logical)).toList = sourceFields39 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics39 (logical : Nat → F) :
    (sourceLookup39).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields39 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup39, sourceExpressions39, sourceFields39, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 250]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 251])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand40 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 95)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 64)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 150))], ⟨⟨1476395013, by decide⟩⟩⟩, 25⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions40 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 252]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 254])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup40 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions40⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields40 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 252]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 254])])).eval (Verification.environment logical)]

theorem source_values40 (logical : Nat → F) :
    (sourceExpressions40.map (Verification.environment logical)).toList = sourceFields40 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics40 (logical : Nat → F) :
    (sourceLookup40).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields40 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup40, sourceExpressions40, sourceFields40, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 252]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 254])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand41 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 96)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 65)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 150))], ⟨⟨133099247, by decide⟩⟩⟩, 26⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions41 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 253]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 254])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup41 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions41⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields41 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 253]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 254])])).eval (Verification.environment logical)]

theorem source_values41 (logical : Nat → F) :
    (sourceExpressions41.map (Verification.environment logical)).toList = sourceFields41 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics41 (logical : Nat → F) :
    (sourceLookup41).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields41 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup41, sourceExpressions41, sourceFields41, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 253]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 254])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand42 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 95)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 68)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 151))], ⟨⟨1476395013, by decide⟩⟩⟩, 27⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions42 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 255]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 257])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup42 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions42⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields42 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 255]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 257])])).eval (Verification.environment logical)]

theorem source_values42 (logical : Nat → F) :
    (sourceExpressions42.map (Verification.environment logical)).toList = sourceFields42 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics42 (logical : Nat → F) :
    (sourceLookup42).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields42 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup42, sourceExpressions42, sourceFields42, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 255]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 257])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand43 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 96)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 69)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 151))], ⟨⟨133099247, by decide⟩⟩⟩, 28⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions43 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 256]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 257])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup43 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions43⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields43 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 256]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 257])])).eval (Verification.environment logical)]

theorem source_values43 (logical : Nat → F) :
    (sourceExpressions43.map (Verification.environment logical)).toList = sourceFields43 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics43 (logical : Nat → F) :
    (sourceLookup43).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields43 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup43, sourceExpressions43, sourceFields43, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 256]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 257])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand44 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 95)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 72)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 152))], ⟨⟨1476395013, by decide⟩⟩⟩, 29⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions44 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 258]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 260])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup44 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions44⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields44 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 258]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 260])])).eval (Verification.environment logical)]

theorem source_values44 (logical : Nat → F) :
    (sourceExpressions44.map (Verification.environment logical)).toList = sourceFields44 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics44 (logical : Nat → F) :
    (sourceLookup44).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields44 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup44, sourceExpressions44, sourceFields44, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 258]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 260])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand45 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 96)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 73)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 152))], ⟨⟨133099247, by decide⟩⟩⟩, 30⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions45 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 259]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 260])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup45 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions45⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields45 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 259]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 260])])).eval (Verification.environment logical)]

theorem source_values45 (logical : Nat → F) :
    (sourceExpressions45.map (Verification.environment logical)).toList = sourceFields45 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics45 (logical : Nat → F) :
    (sourceLookup45).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields45 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup45, sourceExpressions45, sourceFields45, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 259]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 260])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand46 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 95)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 76)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 153))], ⟨⟨1476395013, by decide⟩⟩⟩, 31⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions46 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 261]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 263])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup46 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions46⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields46 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 261]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 263])])).eval (Verification.environment logical)]

theorem source_values46 (logical : Nat → F) :
    (sourceExpressions46.map (Verification.environment logical)).toList = sourceFields46 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics46 (logical : Nat → F) :
    (sourceLookup46).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields46 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup46, sourceExpressions46, sourceFields46, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 261]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 263])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand47 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 96)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 77)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 153))], ⟨⟨133099247, by decide⟩⟩⟩, 32⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions47 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 262]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 263])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup47 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions47⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields47 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 262]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 263])])).eval (Verification.environment logical)]

theorem source_values47 (logical : Nat → F) :
    (sourceExpressions47.map (Verification.environment logical)).toList = sourceFields47 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics47 (logical : Nat → F) :
    (sourceLookup47).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields47 logical = NativeWorkerSetup.rows .bigint 2 index := by
  simpa only [sourceLookup47, sourceExpressions47, sourceFields47, Trace.timestampLookup] using
    timestamp_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 262]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 263])])) logical


end Airbender.Compiler.WorkerConstraints.Bigint
