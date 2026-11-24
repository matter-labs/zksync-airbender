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
noncomputable def operand24 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 24)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 47))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 17))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 59))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 60))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 23⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions24 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 28]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 111])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 81])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 123])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 124])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup24 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions24⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields24 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 28]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 111])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 81])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 123])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 124])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values24 (logical : Nat → F) :
    (sourceExpressions24.map (Verification.environment logical)).toList = sourceFields24 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag24 (logical : Nat → F) :
    ((sourceFields24 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics24 (logical : Nat → F) :
    (sourceLookup24).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields24 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions24.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values24]
    exact source_tag24 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions24 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values24 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values24 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand25 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 48))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 18))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 61))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 62))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 24⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions25 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 112])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 82])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 125])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 126])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup25 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions25⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields25 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 112])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 82])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 125])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 126])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values25 (logical : Nat → F) :
    (sourceExpressions25.map (Verification.environment logical)).toList = sourceFields25 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag25 (logical : Nat → F) :
    ((sourceFields25 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics25 (logical : Nat → F) :
    (sourceLookup25).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields25 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions25.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values25]
    exact source_tag25 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions25 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values25 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values25 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand26 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 25)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 48))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 19))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 63))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 64))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 25⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions26 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 29]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 112])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 83])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 127])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 128])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup26 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions26⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields26 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 29]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 112])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 83])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 127])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 128])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values26 (logical : Nat → F) :
    (sourceExpressions26.map (Verification.environment logical)).toList = sourceFields26 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag26 (logical : Nat → F) :
    ((sourceFields26 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics26 (logical : Nat → F) :
    (sourceLookup26).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields26 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions26.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values26]
    exact source_tag26 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions26 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values26 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values26 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand27 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 65))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 12))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 69))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 70))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 26⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions27 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 129])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 76])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 133])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 134])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup27 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions27⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields27 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 129])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 76])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 133])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 134])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values27 (logical : Nat → F) :
    (sourceExpressions27.map (Verification.environment logical)).toList = sourceFields27 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag27 (logical : Nat → F) :
    ((sourceFields27 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics27 (logical : Nat → F) :
    (sourceLookup27).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields27 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions27.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values27]
    exact source_tag27 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions27 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values27 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values27 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand28 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 28)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 65))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 13))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 71))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 72))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 27⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions28 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 32]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 129])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 77])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 135])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 136])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup28 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions28⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields28 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 32]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 129])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 77])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 135])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 136])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values28 (logical : Nat → F) :
    (sourceExpressions28.map (Verification.environment logical)).toList = sourceFields28 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag28 (logical : Nat → F) :
    ((sourceFields28 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics28 (logical : Nat → F) :
    (sourceLookup28).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields28 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions28.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values28]
    exact source_tag28 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions28 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values28 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values28 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand29 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 66))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 14))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 73))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 74))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 28⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions29 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 130])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 78])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 137])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 138])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup29 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions29⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields29 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 130])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 78])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 137])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 138])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values29 (logical : Nat → F) :
    (sourceExpressions29.map (Verification.environment logical)).toList = sourceFields29 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag29 (logical : Nat → F) :
    ((sourceFields29 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics29 (logical : Nat → F) :
    (sourceLookup29).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields29 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions29.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values29]
    exact source_tag29 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions29 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values29 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values29 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand30 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 29)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 66))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 15))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 75))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 76))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 29⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions30 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 33]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 130])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 79])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 139])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 140])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup30 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions30⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields30 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 33]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 130])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 79])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 139])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 140])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values30 (logical : Nat → F) :
    (sourceExpressions30.map (Verification.environment logical)).toList = sourceFields30 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag30 (logical : Nat → F) :
    ((sourceFields30 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics30 (logical : Nat → F) :
    (sourceLookup30).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields30 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions30.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values30]
    exact source_tag30 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions30 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values30 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values30 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand31 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 67))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 16))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 77))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 78))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 30⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions31 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 131])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 80])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 141])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 142])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup31 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions31⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields31 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 131])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 80])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 141])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 142])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values31 (logical : Nat → F) :
    (sourceExpressions31.map (Verification.environment logical)).toList = sourceFields31 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag31 (logical : Nat → F) :
    ((sourceFields31 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics31 (logical : Nat → F) :
    (sourceLookup31).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields31 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions31.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values31]
    exact source_tag31 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions31 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values31 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values31 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand32 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 33)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 67))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 17))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 79))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 80))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 31⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions32 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 36]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 131])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 81])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 143])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 144])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup32 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions32⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields32 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 36]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 131])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 81])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 143])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 144])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values32 (logical : Nat → F) :
    (sourceExpressions32.map (Verification.environment logical)).toList = sourceFields32 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag32 (logical : Nat → F) :
    ((sourceFields32 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics32 (logical : Nat → F) :
    (sourceLookup32).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields32 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions32.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values32]
    exact source_tag32 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions32 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values32 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values32 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand33 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 68))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 18))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 81))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 82))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 32⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions33 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 132])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 82])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 145])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 146])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup33 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions33⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields33 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 132])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 82])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 145])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 146])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values33 (logical : Nat → F) :
    (sourceExpressions33.map (Verification.environment logical)).toList = sourceFields33 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag33 (logical : Nat → F) :
    ((sourceFields33 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics33 (logical : Nat → F) :
    (sourceLookup33).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields33 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions33.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values33]
    exact source_tag33 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions33 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values33 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values33 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand34 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 34)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 68))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 19))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 83))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 84))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 33⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions34 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 37]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 132])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 83])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 147])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 148])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup34 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions34⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields34 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 37]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 132])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 83])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 147])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 148])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values34 (logical : Nat → F) :
    (sourceExpressions34.map (Verification.environment logical)).toList = sourceFields34 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag34 (logical : Nat → F) :
    ((sourceFields34 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics34 (logical : Nat → F) :
    (sourceLookup34).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields34 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions34.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values34]
    exact source_tag34 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions34 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values34 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values34 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand35 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 85))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 12))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 23))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 89))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 90))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 34⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions35 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 149])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 76])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 87])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 153])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 154])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup35 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions35⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields35 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 149])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 76])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 87])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 153])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 154])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values35 (logical : Nat → F) :
    (sourceExpressions35.map (Verification.environment logical)).toList = sourceFields35 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag35 (logical : Nat → F) :
    ((sourceFields35 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics35 (logical : Nat → F) :
    (sourceLookup35).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields35 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions35.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values35]
    exact source_tag35 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions35 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values35 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values35 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
