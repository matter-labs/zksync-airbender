module
public import Proven.Compiler.WorkerConstraints.Values
public import Proven.Compiler.WorkerConstraints.Setup
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeG
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One actual resolved primitive operand. -/
noncomputable def operand12 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 54)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 33)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 51))], ⟨⟨133099247, by decide⟩⟩⟩, 12⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions12 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 99]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 100])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup12 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions12⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields12 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 99]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 100])])).eval (Verification.environment logical)]

theorem source_values12 (logical : Nat → F) :
    (sourceExpressions12.map (Verification.environment logical)).toList = sourceFields12 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics12 (logical : Nat → F) :
    (sourceLookup12).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields12 logical = NativeWorkerSetup.rows .blakeG 2 index := by
  simpa only [sourceLookup12, sourceExpressions12, sourceFields12, Trace.timestampLookup] using
    timestamp_refinement .blakeG (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 99]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 100])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand13 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 53)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 36)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 52))], ⟨⟨1476395013, by decide⟩⟩⟩, 13⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions13 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 101]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 103])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup13 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions13⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields13 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 101]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 103])])).eval (Verification.environment logical)]

theorem source_values13 (logical : Nat → F) :
    (sourceExpressions13.map (Verification.environment logical)).toList = sourceFields13 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics13 (logical : Nat → F) :
    (sourceLookup13).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields13 logical = NativeWorkerSetup.rows .blakeG 2 index := by
  simpa only [sourceLookup13, sourceExpressions13, sourceFields13, Trace.timestampLookup] using
    timestamp_refinement .blakeG (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 101]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 103])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand14 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 54)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 37)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 52))], ⟨⟨133099247, by decide⟩⟩⟩, 14⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions14 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 102]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 103])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup14 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions14⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields14 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 102]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 103])])).eval (Verification.environment logical)]

theorem source_values14 (logical : Nat → F) :
    (sourceExpressions14.map (Verification.environment logical)).toList = sourceFields14 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics14 (logical : Nat → F) :
    (sourceLookup14).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields14 logical = NativeWorkerSetup.rows .blakeG 2 index := by
  simpa only [sourceLookup14, sourceExpressions14, sourceFields14, Trace.timestampLookup] using
    timestamp_refinement .blakeG (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 102]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 103])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand15 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 53)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 41)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 53))], ⟨⟨1476395013, by decide⟩⟩⟩, 15⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions15 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 104]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 106])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup15 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions15⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields15 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 104]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 106])])).eval (Verification.environment logical)]

theorem source_values15 (logical : Nat → F) :
    (sourceExpressions15.map (Verification.environment logical)).toList = sourceFields15 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics15 (logical : Nat → F) :
    (sourceLookup15).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields15 logical = NativeWorkerSetup.rows .blakeG 2 index := by
  simpa only [sourceLookup15, sourceExpressions15, sourceFields15, Trace.timestampLookup] using
    timestamp_refinement .blakeG (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 104]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 106])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand16 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 54)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 42)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 53))], ⟨⟨133099247, by decide⟩⟩⟩, 16⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions16 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 105]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 106])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup16 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions16⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields16 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 105]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 106])])).eval (Verification.environment logical)]

theorem source_values16 (logical : Nat → F) :
    (sourceExpressions16.map (Verification.environment logical)).toList = sourceFields16 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics16 (logical : Nat → F) :
    (sourceLookup16).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields16 logical = NativeWorkerSetup.rows .blakeG 2 index := by
  simpa only [sourceLookup16, sourceExpressions16, sourceFields16, Trace.timestampLookup] using
    timestamp_refinement .blakeG (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 105]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 106])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand17 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 53)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 46)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 54))], ⟨⟨1476395013, by decide⟩⟩⟩, 17⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions17 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 107]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 109])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup17 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions17⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields17 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 107]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 109])])).eval (Verification.environment logical)]

theorem source_values17 (logical : Nat → F) :
    (sourceExpressions17.map (Verification.environment logical)).toList = sourceFields17 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics17 (logical : Nat → F) :
    (sourceLookup17).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields17 logical = NativeWorkerSetup.rows .blakeG 2 index := by
  simpa only [sourceLookup17, sourceExpressions17, sourceFields17, Trace.timestampLookup] using
    timestamp_refinement .blakeG (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 107]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 109])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand18 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 54)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 47)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 54))], ⟨⟨133099247, by decide⟩⟩⟩, 18⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions18 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 108]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 109])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup18 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions18⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields18 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 108]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 109])])).eval (Verification.environment logical)]

theorem source_values18 (logical : Nat → F) :
    (sourceExpressions18.map (Verification.environment logical)).toList = sourceFields18 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics18 (logical : Nat → F) :
    (sourceLookup18).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields18 logical = NativeWorkerSetup.rows .blakeG 2 index := by
  simpa only [sourceLookup18, sourceExpressions18, sourceFields18, Trace.timestampLookup] using
    timestamp_refinement .blakeG (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 108]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 109])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand19 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨67108864, by decide⟩⟩, (.BaseLayerMemory 2))], ⟨⟨0, by decide⟩⟩⟩, 19⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions19 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨67108864, by decide⟩⟩, .Var 13])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup19 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions19⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields19 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨67108864, by decide⟩⟩, .Var 13])])).eval (Verification.environment logical)]

theorem source_values19 (logical : Nat → F) :
    (sourceExpressions19.map (Verification.environment logical)).toList = sourceFields19 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics19 (logical : Nat → F) :
    (sourceLookup19).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields19 logical = NativeWorkerSetup.rows .blakeG 2 index := by
  simpa only [sourceLookup19, sourceExpressions19, sourceFields19, Trace.timestampLookup] using
    timestamp_refinement .blakeG (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨67108864, by decide⟩⟩, .Var 13])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand20 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨67108864, by decide⟩⟩, (.BaseLayerMemory 34))], ⟨⟨0, by decide⟩⟩⟩, 20⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions20 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨67108864, by decide⟩⟩, .Var 31])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup20 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions20⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields20 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨67108864, by decide⟩⟩, .Var 31])])).eval (Verification.environment logical)]

theorem source_values20 (logical : Nat → F) :
    (sourceExpressions20.map (Verification.environment logical)).toList = sourceFields20 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics20 (logical : Nat → F) :
    (sourceLookup20).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields20 logical = NativeWorkerSetup.rows .blakeG 2 index := by
  simpa only [sourceLookup20, sourceExpressions20, sourceFields20, Trace.timestampLookup] using
    timestamp_refinement .blakeG (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨67108864, by decide⟩⟩, .Var 31])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand21 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268434910, by decide⟩⟩, (.BaseLayerMemory 52)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 48))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 50))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 8))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 15))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 22))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 29))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 40))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 45))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394949, by decide⟩⟩⟩], 0⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions21 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268434910, by decide⟩⟩, .Var 0]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 3])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 5])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 7])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 8])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 9])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 10])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 11])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 12])]), Import.expression (.Sum #[(.Constant ⟨⟨1476394949, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup21 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions21⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields21 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268434910, by decide⟩⟩, .Var 0]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 3])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 5])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 7])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 8])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 9])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 10])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 11])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 12])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394949, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values21 (logical : Nat → F) :
    (sourceExpressions21.map (Verification.environment logical)).toList = sourceFields21 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag21 (logical : Nat → F) :
    ((sourceFields21 logical)[8]?).getD 0 ≠ 0 := by
  change (28 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics21 (logical : Nat → F) :
    (sourceLookup21).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields21 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions21.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values21]
    exact source_tag21 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions21 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values21 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values21 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand22 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 6))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 4))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 7))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 1⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions22 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 43])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 41])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 44])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup22 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions22⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields22 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 43])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 41])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 44])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values22 (logical : Nat → F) :
    (sourceExpressions22.map (Verification.environment logical)).toList = sourceFields22 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag22 (logical : Nat → F) :
    ((sourceFields22 logical)[8]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics22 (logical : Nat → F) :
    (sourceLookup22).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields22 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions22.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values22]
    exact source_tag22 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions22 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values22 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values22 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand23 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 27)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 6))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 6)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 13)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 38)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 0)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 1)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 4))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 8))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 2⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions23 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 27]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 43])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 15]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 19]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 33]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 37]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 38]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 41])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 45])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup23 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions23⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields23 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 27]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 43])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 15]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 19]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 33]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 37]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 38]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 41])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 45])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values23 (logical : Nat → F) :
    (sourceExpressions23.map (Verification.environment logical)).toList = sourceFields23 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag23 (logical : Nat → F) :
    ((sourceFields23 logical)[8]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics23 (logical : Nat → F) :
    (sourceLookup23).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields23 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions23.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values23]
    exact source_tag23 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions23 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values23 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values23 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.BlakeG
