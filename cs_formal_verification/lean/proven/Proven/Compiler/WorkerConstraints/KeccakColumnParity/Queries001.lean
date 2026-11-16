module
public import Proven.Compiler.WorkerConstraints.Values
public import Proven.Compiler.WorkerConstraints.Setup
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One actual resolved primitive operand. -/
noncomputable def operand12 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 74)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 29)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 81))], ⟨⟨133099247, by decide⟩⟩⟩, 12⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions12 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 139]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 140])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup12 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions12⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields12 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 139]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 140])])).eval (Verification.environment logical)]

theorem source_values12 (logical : Nat → F) :
    (sourceExpressions12.map (Verification.environment logical)).toList = sourceFields12 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics12 (logical : Nat → F) :
    (sourceLookup12).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields12 logical = NativeWorkerSetup.rows .columnParity 2 index := by
  simpa only [sourceLookup12, sourceExpressions12, sourceFields12, Trace.timestampLookup] using
    timestamp_refinement .columnParity (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 139]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 140])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand13 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 73)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 32)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 82))], ⟨⟨1476395013, by decide⟩⟩⟩, 13⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions13 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 141]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 143])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup13 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions13⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields13 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 141]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 143])])).eval (Verification.environment logical)]

theorem source_values13 (logical : Nat → F) :
    (sourceExpressions13.map (Verification.environment logical)).toList = sourceFields13 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics13 (logical : Nat → F) :
    (sourceLookup13).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields13 logical = NativeWorkerSetup.rows .columnParity 2 index := by
  simpa only [sourceLookup13, sourceExpressions13, sourceFields13, Trace.timestampLookup] using
    timestamp_refinement .columnParity (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 141]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 143])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand14 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 74)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 33)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 82))], ⟨⟨133099247, by decide⟩⟩⟩, 14⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions14 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 142]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 143])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup14 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions14⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields14 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 142]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 143])])).eval (Verification.environment logical)]

theorem source_values14 (logical : Nat → F) :
    (sourceExpressions14.map (Verification.environment logical)).toList = sourceFields14 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics14 (logical : Nat → F) :
    (sourceLookup14).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields14 logical = NativeWorkerSetup.rows .columnParity 2 index := by
  simpa only [sourceLookup14, sourceExpressions14, sourceFields14, Trace.timestampLookup] using
    timestamp_refinement .columnParity (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 142]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 143])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand15 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 73)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 37)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 83))], ⟨⟨1476395013, by decide⟩⟩⟩, 15⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions15 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 144]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 146])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup15 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions15⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields15 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 144]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 146])])).eval (Verification.environment logical)]

theorem source_values15 (logical : Nat → F) :
    (sourceExpressions15.map (Verification.environment logical)).toList = sourceFields15 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics15 (logical : Nat → F) :
    (sourceLookup15).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields15 logical = NativeWorkerSetup.rows .columnParity 2 index := by
  simpa only [sourceLookup15, sourceExpressions15, sourceFields15, Trace.timestampLookup] using
    timestamp_refinement .columnParity (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 144]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 146])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand16 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 74)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 38)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 83))], ⟨⟨133099247, by decide⟩⟩⟩, 16⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions16 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 145]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 146])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup16 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions16⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields16 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 145]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 146])])).eval (Verification.environment logical)]

theorem source_values16 (logical : Nat → F) :
    (sourceExpressions16.map (Verification.environment logical)).toList = sourceFields16 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics16 (logical : Nat → F) :
    (sourceLookup16).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields16 logical = NativeWorkerSetup.rows .columnParity 2 index := by
  simpa only [sourceLookup16, sourceExpressions16, sourceFields16, Trace.timestampLookup] using
    timestamp_refinement .columnParity (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 145]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 146])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand17 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 73)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 41)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 84))], ⟨⟨1476395013, by decide⟩⟩⟩, 17⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions17 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 147]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 149])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup17 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions17⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields17 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 147]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 149])])).eval (Verification.environment logical)]

theorem source_values17 (logical : Nat → F) :
    (sourceExpressions17.map (Verification.environment logical)).toList = sourceFields17 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics17 (logical : Nat → F) :
    (sourceLookup17).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields17 logical = NativeWorkerSetup.rows .columnParity 2 index := by
  simpa only [sourceLookup17, sourceExpressions17, sourceFields17, Trace.timestampLookup] using
    timestamp_refinement .columnParity (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 147]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 149])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand18 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 74)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 42)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 84))], ⟨⟨133099247, by decide⟩⟩⟩, 18⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions18 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 148]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 149])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup18 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions18⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields18 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 148]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 149])])).eval (Verification.environment logical)]

theorem source_values18 (logical : Nat → F) :
    (sourceExpressions18.map (Verification.environment logical)).toList = sourceFields18 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics18 (logical : Nat → F) :
    (sourceLookup18).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields18 logical = NativeWorkerSetup.rows .columnParity 2 index := by
  simpa only [sourceLookup18, sourceExpressions18, sourceFields18, Trace.timestampLookup] using
    timestamp_refinement .columnParity (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 148]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 149])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand19 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 73)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 46)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 85))], ⟨⟨1476395013, by decide⟩⟩⟩, 19⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions19 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 150]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 152])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup19 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions19⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields19 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 150]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 152])])).eval (Verification.environment logical)]

theorem source_values19 (logical : Nat → F) :
    (sourceExpressions19.map (Verification.environment logical)).toList = sourceFields19 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics19 (logical : Nat → F) :
    (sourceLookup19).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields19 logical = NativeWorkerSetup.rows .columnParity 2 index := by
  simpa only [sourceLookup19, sourceExpressions19, sourceFields19, Trace.timestampLookup] using
    timestamp_refinement .columnParity (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 150]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 152])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand20 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 74)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 47)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 85))], ⟨⟨133099247, by decide⟩⟩⟩, 20⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions20 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 151]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 152])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup20 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions20⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields20 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 151]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 152])])).eval (Verification.environment logical)]

theorem source_values20 (logical : Nat → F) :
    (sourceExpressions20.map (Verification.environment logical)).toList = sourceFields20 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics20 (logical : Nat → F) :
    (sourceLookup20).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields20 logical = NativeWorkerSetup.rows .columnParity 2 index := by
  simpa only [sourceLookup20, sourceExpressions20, sourceFields20, Trace.timestampLookup] using
    timestamp_refinement .columnParity (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 151]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 152])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand21 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 73)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 50)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 86))], ⟨⟨1476395013, by decide⟩⟩⟩, 21⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions21 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 153]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 155])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup21 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions21⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields21 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 153]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 155])])).eval (Verification.environment logical)]

theorem source_values21 (logical : Nat → F) :
    (sourceExpressions21.map (Verification.environment logical)).toList = sourceFields21 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics21 (logical : Nat → F) :
    (sourceLookup21).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields21 logical = NativeWorkerSetup.rows .columnParity 2 index := by
  simpa only [sourceLookup21, sourceExpressions21, sourceFields21, Trace.timestampLookup] using
    timestamp_refinement .columnParity (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 153]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 155])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand22 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 74)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 51)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 86))], ⟨⟨133099247, by decide⟩⟩⟩, 22⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions22 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 154]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 155])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup22 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions22⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields22 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 154]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 155])])).eval (Verification.environment logical)]

theorem source_values22 (logical : Nat → F) :
    (sourceExpressions22.map (Verification.environment logical)).toList = sourceFields22 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics22 (logical : Nat → F) :
    (sourceLookup22).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields22 logical = NativeWorkerSetup.rows .columnParity 2 index := by
  simpa only [sourceLookup22, sourceExpressions22, sourceFields22, Trace.timestampLookup] using
    timestamp_refinement .columnParity (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 154]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 155])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand23 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 73)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 55)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 87))], ⟨⟨1476395013, by decide⟩⟩⟩, 23⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions23 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 156]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 158])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup23 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions23⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields23 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 156]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 158])])).eval (Verification.environment logical)]

theorem source_values23 (logical : Nat → F) :
    (sourceExpressions23.map (Verification.environment logical)).toList = sourceFields23 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics23 (logical : Nat → F) :
    (sourceLookup23).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields23 logical = NativeWorkerSetup.rows .columnParity 2 index := by
  simpa only [sourceLookup23, sourceExpressions23, sourceFields23, Trace.timestampLookup] using
    timestamp_refinement .columnParity (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 156]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 158])])) logical


end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
