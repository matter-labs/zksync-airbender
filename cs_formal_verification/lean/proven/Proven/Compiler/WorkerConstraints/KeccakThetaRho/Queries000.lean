module
public import Proven.Compiler.WorkerConstraints.Values
public import Proven.Compiler.WorkerConstraints.Setup
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One actual resolved primitive operand. -/
noncomputable def operand0 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1073741824, by decide⟩⟩, (.BaseLayerMemory 70)), (⟨⟨939524097, by decide⟩⟩, (.BaseLayerMemory 69))], ⟨⟨0, by decide⟩⟩⟩, 0⟩⟩

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
      ∃ index, sourceFields0 logical = NativeWorkerSetup.rows .thetaRho 2 index := by
  simpa only [sourceLookup0, sourceExpressions0, sourceFields0, Trace.timestampLookup] using
    timestamp_refinement .thetaRho (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741824, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨939524097, by decide⟩⟩, .Var 0])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand1 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨134213359, by decide⟩⟩, (.BaseLayerMemory 69)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 2))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 12))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 21))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 30))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 39))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 48))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 59))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 66))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨2013265793, by decide⟩⟩⟩], 0⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions1 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨134213359, by decide⟩⟩, .Var 0]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 3])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 7])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 8])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 9])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 10])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 11])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 12])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 13])]), Import.expression (.Sum #[(.Constant ⟨⟨2013265793, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup1 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions1⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields1 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨134213359, by decide⟩⟩, .Var 0]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 3])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 7])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 8])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 9])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 10])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 11])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 12])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 13])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨2013265793, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values1 (logical : Nat → F) :
    (sourceExpressions1.map (Verification.environment logical)).toList = sourceFields1 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag1 (logical : Nat → F) :
    ((sourceFields1 logical)[8]?).getD 0 ≠ 0 := by
  change (60 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics1 (logical : Nat → F) :
    (sourceLookup1).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields1 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions1.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values1]
    exact source_tag1 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions1 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values1 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values1 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand2 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 0))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 8))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 12))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 1⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions2 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 64])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 72])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 76])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup2 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions2⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields2 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 64])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 72])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 76])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values2 (logical : Nat → F) :
    (sourceExpressions2.map (Verification.environment logical)).toList = sourceFields2 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag2 (logical : Nat → F) :
    ((sourceFields2 logical)[8]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics2 (logical : Nat → F) :
    (sourceLookup2).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields2 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions2.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values2]
    exact source_tag2 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions2 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values2 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values2 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand3 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 57)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 0))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 64)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 4)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 7)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 8))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 13))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 2⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions3 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 56]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 64])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 60]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 68]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 71]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 72])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 77])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup3 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions3⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields3 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 56]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 64])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 60]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 68]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 71]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 72])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 77])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values3 (logical : Nat → F) :
    (sourceExpressions3.map (Verification.environment logical)).toList = sourceFields3 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag3 (logical : Nat → F) :
    ((sourceFields3 logical)[8]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics3 (logical : Nat → F) :
    (sourceLookup3).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields3 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions3.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values3]
    exact source_tag3 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions3 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values3 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values3 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand4 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 1))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 9))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 14))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 3⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions4 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 65])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 73])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 78])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup4 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions4⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields4 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 65])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 73])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 78])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values4 (logical : Nat → F) :
    (sourceExpressions4.map (Verification.environment logical)).toList = sourceFields4 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag4 (logical : Nat → F) :
    ((sourceFields4 logical)[8]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics4 (logical : Nat → F) :
    (sourceLookup4).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields4 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions4.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values4]
    exact source_tag4 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions4 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values4 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values4 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand5 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 58)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 1))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 65)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 4)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 5)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 9))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 15))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 4⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions5 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 57]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 65])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 61]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 68]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 69]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 73])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 79])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup5 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions5⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields5 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 57]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 65])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 61]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 68]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 69]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 73])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 79])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values5 (logical : Nat → F) :
    (sourceExpressions5.map (Verification.environment logical)).toList = sourceFields5 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag5 (logical : Nat → F) :
    ((sourceFields5 logical)[8]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics5 (logical : Nat → F) :
    (sourceLookup5).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields5 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions5.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values5]
    exact source_tag5 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions5 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values5 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values5 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand6 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 2))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 10))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 16))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 5⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions6 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 66])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 74])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 80])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup6 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions6⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields6 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 66])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 74])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 80])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values6 (logical : Nat → F) :
    (sourceExpressions6.map (Verification.environment logical)).toList = sourceFields6 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag6 (logical : Nat → F) :
    ((sourceFields6 logical)[8]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics6 (logical : Nat → F) :
    (sourceLookup6).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields6 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions6.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values6]
    exact source_tag6 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions6 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values6 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values6 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand7 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 60)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 2))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 67)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 5)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 6)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 10))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 17))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 6⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions7 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 58]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 66])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 62]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 69]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 70]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 74])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 81])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup7 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions7⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields7 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 58]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 66])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 62]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 69]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 70]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 74])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 81])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values7 (logical : Nat → F) :
    (sourceExpressions7.map (Verification.environment logical)).toList = sourceFields7 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag7 (logical : Nat → F) :
    ((sourceFields7 logical)[8]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics7 (logical : Nat → F) :
    (sourceLookup7).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields7 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions7.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values7]
    exact source_tag7 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions7 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values7 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values7 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand8 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 3))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 11))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 18))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 7⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions8 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 67])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 75])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 82])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup8 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions8⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields8 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 67])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 75])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 82])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values8 (logical : Nat → F) :
    (sourceExpressions8.map (Verification.environment logical)).toList = sourceFields8 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag8 (logical : Nat → F) :
    ((sourceFields8 logical)[8]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics8 (logical : Nat → F) :
    (sourceLookup8).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields8 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions8.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values8]
    exact source_tag8 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions8 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values8 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values8 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand9 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 61)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 3))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 68)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 6)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 7)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 11))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 19))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 8⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions9 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 59]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 67])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 63]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 70]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 71]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 75])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 83])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup9 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions9⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields9 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 59]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 67])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 63]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 70]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 71]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 75])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 83])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values9 (logical : Nat → F) :
    (sourceExpressions9.map (Verification.environment logical)).toList = sourceFields9 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag9 (logical : Nat → F) :
    ((sourceFields9 logical)[8]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics9 (logical : Nat → F) :
    (sourceLookup9).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields9 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions9.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values9]
    exact source_tag9 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions9 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values9 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values9 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand10 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 2))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 69))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 4))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 20))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 21))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 22))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 23))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1744830339, by decide⟩⟩⟩], 9⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions10 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 3])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 0])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 5])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 86])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨1744830339, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup10 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions10⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields10 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 3])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 0])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 5])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 86])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1744830339, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values10 (logical : Nat → F) :
    (sourceExpressions10.map (Verification.environment logical)).toList = sourceFields10 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag10 (logical : Nat → F) :
    ((sourceFields10 logical)[8]?).getD 0 ≠ 0 := by
  change (59 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics10 (logical : Nat → F) :
    (sourceLookup10).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields10 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions10.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values10]
    exact source_tag10 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions10 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values10 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values10 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand11 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 25))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 12))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 29))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 30))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 10⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions11 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 89])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 76])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 93])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 94])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup11 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions11⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields11 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 89])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 76])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 93])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 94])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values11 (logical : Nat → F) :
    (sourceExpressions11.map (Verification.environment logical)).toList = sourceFields11 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag11 (logical : Nat → F) :
    ((sourceFields11 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics11 (logical : Nat → F) :
    (sourceLookup11).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields11 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions11.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values11]
    exact source_tag11 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions11 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values11 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values11 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
