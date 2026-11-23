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
noncomputable def operand24 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 9))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 5))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 10))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 3⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions24 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 46])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 42])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 47])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup24 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions24⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields24 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 46])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 42])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 47])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values24 (logical : Nat → F) :
    (sourceExpressions24.map (Verification.environment logical)).toList = sourceFields24 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag24 (logical : Nat → F) :
    ((sourceFields24 logical)[8]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics24 (logical : Nat → F) :
    (sourceLookup24).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields24 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions24.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values24]
    exact source_tag24 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions24 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values24 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values24 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand25 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 28)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 9))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 7)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 14)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 39)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 0)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 1)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 2)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 3)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 5))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 11))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 4⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions25 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 28]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 46])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 16]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 20]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 34]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 37]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 38]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 39]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 40]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 42])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 48])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup25 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions25⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields25 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 28]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 46])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 16]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 20]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 34]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 37]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 38]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 39]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 40]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 42])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 48])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values25 (logical : Nat → F) :
    (sourceExpressions25.map (Verification.environment logical)).toList = sourceFields25 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag25 (logical : Nat → F) :
    ((sourceFields25 logical)[8]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics25 (logical : Nat → F) :
    (sourceLookup25).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields25 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions25.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values25]
    exact source_tag25 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions25 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values25 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values25 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand26 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 18))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 14))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 20))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨536870876, by decide⟩⟩⟩], 5⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions26 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 55])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 51])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 57])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨536870876, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup26 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions26⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields26 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 55])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 51])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 57])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨536870876, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values26 (logical : Nat → F) :
    (sourceExpressions26.map (Verification.environment logical)).toList = sourceFields26 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag26 (logical : Nat → F) :
    ((sourceFields26 logical)[8]?).getD 0 ≠ 0 := by
  change (17 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics26 (logical : Nat → F) :
    (sourceLookup26).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields26 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions26.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values26]
    exact source_tag26 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions26 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values26 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values26 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand27 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 19))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 15))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 21))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 6⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions27 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 56])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 52])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 58])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup27 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions27⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields27 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 56])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 52])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 58])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values27 (logical : Nat → F) :
    (sourceExpressions27.map (Verification.environment logical)).toList = sourceFields27 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag27 (logical : Nat → F) :
    ((sourceFields27 logical)[8]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics27 (logical : Nat → F) :
    (sourceLookup27).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields27 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions27.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values27]
    exact source_tag27 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions27 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values27 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values27 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand28 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 13)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 18)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 19))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 20)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 10)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 11)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 12)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 14)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 15))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 22))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨805306330, by decide⟩⟩⟩], 7⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions28 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 19]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 55]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 56])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 23]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 47]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 48]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 49]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 51]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 52])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 59])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨805306330, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup28 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions28⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields28 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 19]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 55]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 56])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 23]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 47]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 48]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 49]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 51]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 52])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 59])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨805306330, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values28 (logical : Nat → F) :
    (sourceExpressions28.map (Verification.environment logical)).toList = sourceFields28 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag28 (logical : Nat → F) :
    ((sourceFields28 logical)[8]?).getD 0 ≠ 0 := by
  change (18 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics28 (logical : Nat → F) :
    (sourceLookup28).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields28 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions28.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values28]
    exact source_tag28 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions28 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values28 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values28 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand29 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 23))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 16))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 25))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨536870876, by decide⟩⟩⟩], 8⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions29 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 60])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 53])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 62])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨536870876, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup29 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions29⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields29 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 60])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 53])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 62])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨536870876, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values29 (logical : Nat → F) :
    (sourceExpressions29.map (Verification.environment logical)).toList = sourceFields29 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag29 (logical : Nat → F) :
    ((sourceFields29 logical)[8]?).getD 0 ≠ 0 := by
  change (17 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics29 (logical : Nat → F) :
    (sourceLookup29).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields29 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions29.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values29]
    exact source_tag29 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions29 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values29 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values29 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand30 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 17))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 26))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 9⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions30 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 61])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 54])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 63])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup30 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions30⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields30 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 61])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 54])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 63])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values30 (logical : Nat → F) :
    (sourceExpressions30.map (Verification.environment logical)).toList = sourceFields30 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag30 (logical : Nat → F) :
    ((sourceFields30 logical)[8]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics30 (logical : Nat → F) :
    (sourceLookup30).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields30 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions30.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values30]
    exact source_tag30 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions30 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values30 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values30 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand31 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 14)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 21)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 7)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 8)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 12)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 13)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 16)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 17))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 27))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨805306330, by decide⟩⟩⟩], 10⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions31 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 20]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 60]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 61])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 24]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 44]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 45]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 49]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 50]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 53]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 54])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 64])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨805306330, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup31 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions31⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields31 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 20]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 60]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 61])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 24]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 44]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 45]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 49]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 50]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 53]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 54])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 64])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨805306330, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values31 (logical : Nat → F) :
    (sourceExpressions31.map (Verification.environment logical)).toList = sourceFields31 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag31 (logical : Nat → F) :
    ((sourceFields31 logical)[8]?).getD 0 ≠ 0 := by
  change (18 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics31 (logical : Nat → F) :
    (sourceLookup31).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields31 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions31.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values31]
    exact source_tag31 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions31 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values31 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values31 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand32 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 10))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 32))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 34))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 11⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions32 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 47])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 69])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 71])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup32 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions32⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields32 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 47])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 69])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 71])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values32 (logical : Nat → F) :
    (sourceExpressions32.map (Verification.environment logical)).toList = sourceFields32 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag32 (logical : Nat → F) :
    ((sourceFields32 logical)[8]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics32 (logical : Nat → F) :
    (sourceLookup32).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields32 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions32.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values32]
    exact source_tag32 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions32 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values32 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values32 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand33 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 11))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 6)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 13)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 38)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 43)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 0)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 1)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 25)), (⟨⟨134217727, by decide⟩⟩, (.BaseLayerWitness 26)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 28)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 29)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 32))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 35))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 12⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions33 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 48])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 15]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 19]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 33]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 35]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 37]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 38]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 59]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 62]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 63]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 65]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 66]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 69])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 72])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup33 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions33⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields33 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 48])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 15]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 19]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 33]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 35]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 37]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 38]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 59]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 62]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 63]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 65]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 66]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 69])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 72])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values33 (logical : Nat → F) :
    (sourceExpressions33.map (Verification.environment logical)).toList = sourceFields33 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag33 (logical : Nat → F) :
    ((sourceFields33 logical)[8]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics33 (logical : Nat → F) :
    (sourceLookup33).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields33 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions33.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values33]
    exact source_tag33 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions33 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values33 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values33 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand34 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 7))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 33))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 36))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 13⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions34 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 44])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 70])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 73])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup34 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions34⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields34 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 44])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 70])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 73])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values34 (logical : Nat → F) :
    (sourceExpressions34.map (Verification.environment logical)).toList = sourceFields34 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag34 (logical : Nat → F) :
    ((sourceFields34 logical)[8]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics34 (logical : Nat → F) :
    (sourceLookup34).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields34 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions34.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values34]
    exact source_tag34 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions34 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values34 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values34 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand35 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 8))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 7)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 14)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 39)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 44)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 0)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 1)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 2)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 3)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨134217727, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 27)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 28)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 29)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 30)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 31)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 33))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 37))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 14⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions35 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 45])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 16]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 20]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 34]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 36]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 37]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 38]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 39]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 40]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 57]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 58]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 64]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 65]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 66]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 67]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 68]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 70])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 74])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup35 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions35⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields35 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 45])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 16]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 20]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 34]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 36]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 37]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 38]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 39]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 40]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 57]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 58]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 64]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 65]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 66]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 67]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 68]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 70])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 74])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values35 (logical : Nat → F) :
    (sourceExpressions35.map (Verification.environment logical)).toList = sourceFields35 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag35 (logical : Nat → F) :
    ((sourceFields35 logical)[8]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics35 (logical : Nat → F) :
    (sourceLookup35).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields35 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions35.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values35]
    exact source_tag35 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions35 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values35 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values35 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.BlakeG
