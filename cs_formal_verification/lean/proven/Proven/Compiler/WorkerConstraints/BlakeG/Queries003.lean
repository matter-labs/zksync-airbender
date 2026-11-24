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
noncomputable def operand36 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨268435422, by decide⟩⟩, (.BaseLayerWitness 25))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 40))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 42))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 15⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions36 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 59]), (.Product #[.Constant ⟨⟨268435422, by decide⟩⟩, .Var 62])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 77])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 79])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup36 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions36⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields36 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 59]), (.Product #[.Constant ⟨⟨268435422, by decide⟩⟩, .Var 62])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 77])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 79])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values36 (logical : Nat → F) :
    (sourceExpressions36.map (Verification.environment logical)).toList = sourceFields36 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag36 (logical : Nat → F) :
    ((sourceFields36 logical)[8]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics36 (logical : Nat → F) :
    (sourceLookup36).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields36 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions36.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values36]
    exact source_tag36 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions36 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values36 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values36 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand37 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 26))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 20)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 10)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 11)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 12)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 35)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 36)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 38)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 40))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 43))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 16⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions37 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 63])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 23]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 47]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 48]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 49]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 72]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 73]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 75]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 77])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 80])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup37 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions37⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields37 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 63])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 23]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 47]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 48]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 49]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 72]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 73]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 75]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 77])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 80])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values37 (logical : Nat → F) :
    (sourceExpressions37.map (Verification.environment logical)).toList = sourceFields37 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag37 (logical : Nat → F) :
    ((sourceFields37 logical)[8]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics37 (logical : Nat → F) :
    (sourceLookup37).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields37 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions37.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values37]
    exact source_tag37 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions37 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values37 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values37 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand38 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435422, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 27))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 41))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 44))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 17⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions38 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435422, by decide⟩⟩, .Var 57]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 64])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 78])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 81])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup38 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions38⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields38 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435422, by decide⟩⟩, .Var 57]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 64])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 78])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 81])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values38 (logical : Nat → F) :
    (sourceExpressions38.map (Verification.environment logical)).toList = sourceFields38 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag38 (logical : Nat → F) :
    ((sourceFields38 logical)[8]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics38 (logical : Nat → F) :
    (sourceLookup38).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields38 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions38.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values38]
    exact source_tag38 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions38 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values38 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values38 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand39 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 21))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 21)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 7)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 8)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 12)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 13)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 34)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 37)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 38)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 39)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 41))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 45))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 18⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions39 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 58])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 24]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 44]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 45]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 49]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 50]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 71]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 74]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 75]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 76]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 78])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 82])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup39 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeG).toRaw, sourceExpressions39⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields39 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 58])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 24]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 44]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 45]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 49]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 50]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 71]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 74]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 75]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 76]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 78])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 82])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values39 (logical : Nat → F) :
    (sourceExpressions39.map (Verification.environment logical)).toList = sourceFields39 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag39 (logical : Nat → F) :
    ((sourceFields39 logical)[8]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics39 (logical : Nat → F) :
    (sourceLookup39).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields39 logical = NativeWorkerSetup.rows .blakeG 0 index := by
  have tag : (((sourceExpressions39.map (Verification.environment logical)).toList)[width .blakeG - 1]?).getD 0 ≠ 0 := by
    rw [source_values39]
    exact source_tag39 logical
  have equivalent := generic_lookup_refinement .blakeG sourceExpressions39 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values39 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values39 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.BlakeG
