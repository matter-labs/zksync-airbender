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
noncomputable def operand24 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 74)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 56)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 87))], ⟨⟨133099247, by decide⟩⟩⟩, 24⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions24 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 157]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 158])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup24 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions24⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields24 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 157]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 158])])).eval (Verification.environment logical)]

theorem source_values24 (logical : Nat → F) :
    (sourceExpressions24.map (Verification.environment logical)).toList = sourceFields24 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics24 (logical : Nat → F) :
    (sourceLookup24).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields24 logical = NativeWorkerSetup.rows .columnParity 2 index := by
  simpa only [sourceLookup24, sourceExpressions24, sourceFields24, Trace.timestampLookup] using
    timestamp_refinement .columnParity (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 157]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 158])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand25 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 73)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 59)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 88))], ⟨⟨1476395013, by decide⟩⟩⟩, 25⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions25 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 159]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 161])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup25 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions25⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields25 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 159]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 161])])).eval (Verification.environment logical)]

theorem source_values25 (logical : Nat → F) :
    (sourceExpressions25.map (Verification.environment logical)).toList = sourceFields25 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics25 (logical : Nat → F) :
    (sourceLookup25).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields25 logical = NativeWorkerSetup.rows .columnParity 2 index := by
  simpa only [sourceLookup25, sourceExpressions25, sourceFields25, Trace.timestampLookup] using
    timestamp_refinement .columnParity (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 159]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 161])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand26 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 74)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 60)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 88))], ⟨⟨133099247, by decide⟩⟩⟩, 26⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions26 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 160]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 161])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup26 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions26⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields26 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 160]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 161])])).eval (Verification.environment logical)]

theorem source_values26 (logical : Nat → F) :
    (sourceExpressions26.map (Verification.environment logical)).toList = sourceFields26 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics26 (logical : Nat → F) :
    (sourceLookup26).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields26 logical = NativeWorkerSetup.rows .columnParity 2 index := by
  simpa only [sourceLookup26, sourceExpressions26, sourceFields26, Trace.timestampLookup] using
    timestamp_refinement .columnParity (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 160]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 161])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand27 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 73)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 66)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 89))], ⟨⟨1476395013, by decide⟩⟩⟩, 27⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions27 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 162]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 164])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup27 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions27⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields27 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 162]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 164])])).eval (Verification.environment logical)]

theorem source_values27 (logical : Nat → F) :
    (sourceExpressions27.map (Verification.environment logical)).toList = sourceFields27 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics27 (logical : Nat → F) :
    (sourceLookup27).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields27 logical = NativeWorkerSetup.rows .columnParity 2 index := by
  simpa only [sourceLookup27, sourceExpressions27, sourceFields27, Trace.timestampLookup] using
    timestamp_refinement .columnParity (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 162]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 164])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand28 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 74)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 67)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 89))], ⟨⟨133099247, by decide⟩⟩⟩, 28⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions28 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 163]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 164])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup28 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions28⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields28 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 163]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 164])])).eval (Verification.environment logical)]

theorem source_values28 (logical : Nat → F) :
    (sourceExpressions28.map (Verification.environment logical)).toList = sourceFields28 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics28 (logical : Nat → F) :
    (sourceLookup28).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields28 logical = NativeWorkerSetup.rows .columnParity 2 index := by
  simpa only [sourceLookup28, sourceExpressions28, sourceFields28, Trace.timestampLookup] using
    timestamp_refinement .columnParity (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 163]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 164])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand29 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨134213359, by decide⟩⟩, (.BaseLayerMemory 72)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 2))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 14))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 27))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 36))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 45))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 54))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 63))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨536870780, by decide⟩⟩⟩], 0⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions29 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨134213359, by decide⟩⟩, .Var 0]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 3])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 7])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 8])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 9])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 10])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 11])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 12])]), Import.expression (.Sum #[(.Constant ⟨⟨536870780, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup29 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions29⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields29 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨134213359, by decide⟩⟩, .Var 0]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 3])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 7])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 8])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 9])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 10])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 11])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 12])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨536870780, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values29 (logical : Nat → F) :
    (sourceExpressions29.map (Verification.environment logical)).toList = sourceFields29 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag29 (logical : Nat → F) :
    ((sourceFields29 logical)[7]?).getD 0 ≠ 0 := by
  change (62 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics29 (logical : Nat → F) :
    (sourceLookup29).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields29 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions29.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values29]
    exact source_tag29 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions29 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values29 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values29 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand30 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 2))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 72))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 4))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 0))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨805306234, by decide⟩⟩⟩], 1⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions30 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 3])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 0])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 5])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 47])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨805306234, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup30 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions30⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields30 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 3])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 0])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 5])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 47])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨805306234, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values30 (logical : Nat → F) :
    (sourceExpressions30.map (Verification.environment logical)).toList = sourceFields30 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag30 (logical : Nat → F) :
    ((sourceFields30 logical)[7]?).getD 0 ≠ 0 := by
  change (63 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics30 (logical : Nat → F) :
    (sourceLookup30).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields30 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions30.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values30]
    exact source_tag30 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions30 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values30 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values30 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand31 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 1))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 0))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 4)), (⟨⟨268435422, by decide⟩⟩, (.BaseLayerWitness 5))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨134217647, by decide⟩⟩⟩], 2⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions31 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 48])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 47])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 51]), (.Product #[.Constant ⟨⟨268435422, by decide⟩⟩, .Var 52])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨134217647, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup31 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions31⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields31 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 48])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 47])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 51]), (.Product #[.Constant ⟨⟨268435422, by decide⟩⟩, .Var 52])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨134217647, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values31 (logical : Nat → F) :
    (sourceExpressions31.map (Verification.environment logical)).toList = sourceFields31 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag31 (logical : Nat → F) :
    ((sourceFields31 logical)[7]?).getD 0 ≠ 0 := by
  change (38 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics31 (logical : Nat → F) :
    (sourceLookup31).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields31 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions31.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values31]
    exact source_tag31 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions31 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values31 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values31 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand32 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 12)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 1))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 0))], ⟨⟨536870844, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 15)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 4)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 5))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨134217647, by decide⟩⟩⟩], 3⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions32 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 15]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 48])]), Import.expression (.Sum #[(.Constant ⟨⟨536870844, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 47])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 17]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 51]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 52])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨134217647, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup32 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions32⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields32 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 15]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 48])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨536870844, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 47])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 17]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 51]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 52])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨134217647, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values32 (logical : Nat → F) :
    (sourceExpressions32.map (Verification.environment logical)).toList = sourceFields32 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag32 (logical : Nat → F) :
    ((sourceFields32 logical)[7]?).getD 0 ≠ 0 := by
  change (38 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics32 (logical : Nat → F) :
    (sourceLookup32).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields32 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions32.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values32]
    exact source_tag32 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions32 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values32 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values32 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand33 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 13)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 2))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 0))], ⟨⟨1610612532, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 16)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 7)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 8))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨134217647, by decide⟩⟩⟩], 4⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions33 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 16]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 49])]), Import.expression (.Sum #[(.Constant ⟨⟨1610612532, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 47])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 18]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 54]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 55])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨134217647, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup33 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions33⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields33 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 16]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 49])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1610612532, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 47])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 18]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 54]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 55])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨134217647, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values33 (logical : Nat → F) :
    (sourceExpressions33.map (Verification.environment logical)).toList = sourceFields33 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag33 (logical : Nat → F) :
    ((sourceFields33 logical)[7]?).getD 0 ≠ 0 := by
  change (38 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics33 (logical : Nat → F) :
    (sourceLookup33).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields33 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions33.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values33]
    exact source_tag33 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions33 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values33 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values33 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand34 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 20)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 3))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 0))], ⟨⟨1744829987, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 22)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 13)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 14))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨134217647, by decide⟩⟩⟩], 5⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions34 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 20]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 50])]), Import.expression (.Sum #[(.Constant ⟨⟨1744829987, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 47])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 22]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 60]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 61])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨134217647, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup34 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions34⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields34 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 20]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 50])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1744829987, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 47])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 22]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 60]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 61])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨134217647, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values34 (logical : Nat → F) :
    (sourceExpressions34.map (Verification.environment logical)).toList = sourceFields34 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag34 (logical : Nat → F) :
    ((sourceFields34 logical)[7]?).getD 0 ≠ 0 := by
  change (38 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics34 (logical : Nat → F) :
    (sourceLookup34).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields34 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions34.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values34]
    exact source_tag34 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions34 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values34 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values34 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand35 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 4))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 16))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 28))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 40))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 52))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 64))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741688, by decide⟩⟩⟩], 6⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions35 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 51])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 63])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 75])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 99])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 111])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup35 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions35⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields35 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 51])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 63])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 75])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 99])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 111])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values35 (logical : Nat → F) :
    (sourceExpressions35.map (Verification.environment logical)).toList = sourceFields35 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag35 (logical : Nat → F) :
    ((sourceFields35 logical)[7]?).getD 0 ≠ 0 := by
  change (64 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics35 (logical : Nat → F) :
    (sourceLookup35).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields35 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions35.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values35]
    exact source_tag35 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions35 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values35 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values35 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
