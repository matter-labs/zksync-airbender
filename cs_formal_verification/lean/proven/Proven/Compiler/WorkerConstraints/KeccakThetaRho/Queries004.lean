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
noncomputable def operand48 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 51)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 107))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 17))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 119))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 120))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 47⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions48 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 52]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 171])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 81])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 183])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 184])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup48 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions48⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields48 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 52]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 171])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 81])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 183])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 184])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values48 (logical : Nat → F) :
    (sourceExpressions48.map (Verification.environment logical)).toList = sourceFields48 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag48 (logical : Nat → F) :
    ((sourceFields48 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics48 (logical : Nat → F) :
    (sourceLookup48).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields48 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions48.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values48]
    exact source_tag48 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions48 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values48 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values48 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand49 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 108))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 18))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 121))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 122))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 48⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions49 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 172])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 82])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 185])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 186])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup49 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions49⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields49 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 172])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 82])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 185])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 186])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values49 (logical : Nat → F) :
    (sourceExpressions49.map (Verification.environment logical)).toList = sourceFields49 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag49 (logical : Nat → F) :
    ((sourceFields49 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics49 (logical : Nat → F) :
    (sourceLookup49).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields49 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions49.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values49]
    exact source_tag49 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions49 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values49 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values49 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand50 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 6))], ⟨⟨0, by decide⟩⟩⟩, 1⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions50 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 14])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup50 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions50⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields50 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 14])])).eval (Verification.environment logical)]

theorem source_values50 (logical : Nat → F) :
    (sourceExpressions50.map (Verification.environment logical)).toList = sourceFields50 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics50 (logical : Nat → F) :
    (sourceLookup50).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields50 logical = NativeWorkerSetup.rows .thetaRho 2 index := by
  simpa only [sourceLookup50, sourceExpressions50, sourceFields50, Trace.timestampLookup] using
    timestamp_refinement .thetaRho (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 14])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand51 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 52)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 108))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 19))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 123))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 124))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 49⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions51 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 53]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 172])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 83])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 187])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 188])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup51 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions51⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields51 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 53]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 172])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 83])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 187])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 188])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values51 (logical : Nat → F) :
    (sourceExpressions51.map (Verification.environment logical)).toList = sourceFields51 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag51 (logical : Nat → F) :
    ((sourceFields51 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics51 (logical : Nat → F) :
    (sourceLookup51).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields51 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions51.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values51]
    exact source_tag51 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions51 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values51 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values51 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
