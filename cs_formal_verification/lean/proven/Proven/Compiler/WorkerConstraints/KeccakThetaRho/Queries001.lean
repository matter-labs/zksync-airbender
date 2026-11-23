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
noncomputable def operand12 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 10)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 25))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 13))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 31))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 32))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 11⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions12 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 16]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 89])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 77])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 95])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 96])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup12 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions12⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields12 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 16]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 89])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 77])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 95])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 96])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values12 (logical : Nat → F) :
    (sourceExpressions12.map (Verification.environment logical)).toList = sourceFields12 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag12 (logical : Nat → F) :
    ((sourceFields12 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics12 (logical : Nat → F) :
    (sourceLookup12).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields12 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions12.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values12]
    exact source_tag12 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions12 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values12 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values12 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand13 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 26))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 14))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 33))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 34))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 12⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions13 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 90])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 78])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 97])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 98])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup13 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions13⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields13 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 90])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 78])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 97])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 98])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values13 (logical : Nat → F) :
    (sourceExpressions13.map (Verification.environment logical)).toList = sourceFields13 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag13 (logical : Nat → F) :
    ((sourceFields13 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics13 (logical : Nat → F) :
    (sourceLookup13).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields13 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions13.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values13]
    exact source_tag13 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions13 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values13 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values13 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand14 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 11)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 26))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 15))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 35))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 36))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 13⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions14 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 17]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 90])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 79])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 99])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 100])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup14 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions14⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields14 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 17]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 90])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 79])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 99])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 100])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values14 (logical : Nat → F) :
    (sourceExpressions14.map (Verification.environment logical)).toList = sourceFields14 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag14 (logical : Nat → F) :
    ((sourceFields14 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics14 (logical : Nat → F) :
    (sourceLookup14).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields14 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions14.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values14]
    exact source_tag14 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions14 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values14 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values14 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand15 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 27))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 16))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 37))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 38))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 14⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions15 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 91])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 80])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 101])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 102])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup15 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions15⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields15 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 91])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 80])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 101])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 102])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values15 (logical : Nat → F) :
    (sourceExpressions15.map (Verification.environment logical)).toList = sourceFields15 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag15 (logical : Nat → F) :
    ((sourceFields15 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics15 (logical : Nat → F) :
    (sourceLookup15).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields15 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions15.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values15]
    exact source_tag15 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions15 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values15 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values15 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand16 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 15)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 27))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 17))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 39))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 40))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 15⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions16 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 20]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 91])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 81])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 103])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 104])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup16 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions16⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields16 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 20]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 91])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 81])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 103])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 104])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values16 (logical : Nat → F) :
    (sourceExpressions16.map (Verification.environment logical)).toList = sourceFields16 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag16 (logical : Nat → F) :
    ((sourceFields16 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics16 (logical : Nat → F) :
    (sourceLookup16).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields16 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions16.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values16]
    exact source_tag16 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions16 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values16 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values16 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand17 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 28))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 18))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 41))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 42))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 16⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions17 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 92])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 82])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 105])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 106])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup17 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions17⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields17 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 92])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 82])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 105])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 106])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values17 (logical : Nat → F) :
    (sourceExpressions17.map (Verification.environment logical)).toList = sourceFields17 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag17 (logical : Nat → F) :
    ((sourceFields17 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics17 (logical : Nat → F) :
    (sourceLookup17).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields17 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions17.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values17]
    exact source_tag17 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions17 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values17 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values17 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand18 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 16)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 28))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 19))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨805306362, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 43))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 44))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 17⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions18 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 21]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 92])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 83])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 107])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 108])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup18 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions18⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields18 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 21]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 92])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 83])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨805306362, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 107])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 108])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values18 (logical : Nat → F) :
    (sourceExpressions18.map (Verification.environment logical)).toList = sourceFields18 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag18 (logical : Nat → F) :
    ((sourceFields18 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics18 (logical : Nat → F) :
    (sourceLookup18).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields18 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions18.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values18]
    exact source_tag18 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions18 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values18 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values18 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand19 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 45))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 12))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 49))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 50))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 18⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions19 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 109])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 76])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 113])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 114])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup19 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions19⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields19 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 109])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 76])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 113])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 114])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values19 (logical : Nat → F) :
    (sourceExpressions19.map (Verification.environment logical)).toList = sourceFields19 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag19 (logical : Nat → F) :
    ((sourceFields19 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics19 (logical : Nat → F) :
    (sourceLookup19).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields19 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions19.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values19]
    exact source_tag19 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions19 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values19 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values19 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand20 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 19)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 45))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 13))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 51))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 52))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 19⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions20 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 24]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 109])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 77])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 115])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 116])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup20 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions20⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields20 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 24]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 109])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 77])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 115])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 116])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values20 (logical : Nat → F) :
    (sourceExpressions20.map (Verification.environment logical)).toList = sourceFields20 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag20 (logical : Nat → F) :
    ((sourceFields20 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics20 (logical : Nat → F) :
    (sourceLookup20).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields20 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions20.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values20]
    exact source_tag20 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions20 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values20 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values20 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand21 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 46))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 14))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 53))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 54))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 20⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions21 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 110])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 78])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 117])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 118])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup21 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions21⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields21 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 110])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 78])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 117])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 118])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values21 (logical : Nat → F) :
    (sourceExpressions21.map (Verification.environment logical)).toList = sourceFields21 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag21 (logical : Nat → F) :
    ((sourceFields21 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics21 (logical : Nat → F) :
    (sourceLookup21).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields21 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions21.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values21]
    exact source_tag21 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions21 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values21 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values21 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand22 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 20)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 46))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 15))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 55))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 56))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 21⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions22 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 25]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 110])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 79])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 119])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 120])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup22 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions22⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields22 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 25]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 110])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 79])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 119])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 120])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values22 (logical : Nat → F) :
    (sourceExpressions22.map (Verification.environment logical)).toList = sourceFields22 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag22 (logical : Nat → F) :
    ((sourceFields22 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics22 (logical : Nat → F) :
    (sourceLookup22).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields22 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions22.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values22]
    exact source_tag22 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions22 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values22 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values22 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand23 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 47))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 16))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1073741816, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 57))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 58))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 22⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions23 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 111])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 80])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 121])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 122])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup23 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions23⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields23 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 111])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 80])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1073741816, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 121])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 122])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values23 (logical : Nat → F) :
    (sourceExpressions23.map (Verification.environment logical)).toList = sourceFields23 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag23 (logical : Nat → F) :
    ((sourceFields23 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics23 (logical : Nat → F) :
    (sourceLookup23).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields23 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions23.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values23]
    exact source_tag23 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions23 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values23 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values23 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
