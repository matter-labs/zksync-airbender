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
noncomputable def operand36 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 37)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 85))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 13))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 23))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 91))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 92))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 35⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions36 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 40]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 149])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 77])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 87])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 155])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 156])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup36 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions36⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields36 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 40]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 149])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 77])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 87])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 155])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 156])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values36 (logical : Nat → F) :
    (sourceExpressions36.map (Verification.environment logical)).toList = sourceFields36 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag36 (logical : Nat → F) :
    ((sourceFields36 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics36 (logical : Nat → F) :
    (sourceLookup36).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields36 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions36.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values36]
    exact source_tag36 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions36 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values36 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values36 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand37 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 86))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 14))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 23))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 93))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 94))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 36⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions37 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 150])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 78])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 87])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 157])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 158])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup37 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions37⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields37 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 150])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 78])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 87])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 157])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 158])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values37 (logical : Nat → F) :
    (sourceExpressions37.map (Verification.environment logical)).toList = sourceFields37 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag37 (logical : Nat → F) :
    ((sourceFields37 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics37 (logical : Nat → F) :
    (sourceLookup37).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields37 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions37.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values37]
    exact source_tag37 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions37 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values37 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values37 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand38 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 38)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 86))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 15))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 23))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 95))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 96))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 37⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions38 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 41]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 150])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 79])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 87])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 159])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 160])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup38 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions38⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields38 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 41]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 150])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 79])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 87])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 159])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 160])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values38 (logical : Nat → F) :
    (sourceExpressions38.map (Verification.environment logical)).toList = sourceFields38 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag38 (logical : Nat → F) :
    ((sourceFields38 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics38 (logical : Nat → F) :
    (sourceLookup38).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields38 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions38.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values38]
    exact source_tag38 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions38 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values38 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values38 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand39 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 87))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 16))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 23))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 97))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 98))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 38⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions39 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 151])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 80])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 87])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 161])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 162])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup39 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions39⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields39 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 151])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 80])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 87])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 161])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 162])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values39 (logical : Nat → F) :
    (sourceExpressions39.map (Verification.environment logical)).toList = sourceFields39 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag39 (logical : Nat → F) :
    ((sourceFields39 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics39 (logical : Nat → F) :
    (sourceLookup39).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields39 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions39.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values39]
    exact source_tag39 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions39 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values39 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values39 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand40 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 42)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 87))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 17))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 23))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 99))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 100))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 39⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions40 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 44]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 151])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 81])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 87])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 163])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 164])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup40 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions40⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields40 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 44]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 151])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 81])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 87])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 163])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 164])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values40 (logical : Nat → F) :
    (sourceExpressions40.map (Verification.environment logical)).toList = sourceFields40 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag40 (logical : Nat → F) :
    ((sourceFields40 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics40 (logical : Nat → F) :
    (sourceLookup40).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields40 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions40.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values40]
    exact source_tag40 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions40 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values40 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values40 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand41 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 88))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 18))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 23))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 101))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 102))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 40⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions41 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 152])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 82])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 87])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 165])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 166])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup41 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions41⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields41 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 152])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 82])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 87])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 165])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 166])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values41 (logical : Nat → F) :
    (sourceExpressions41.map (Verification.environment logical)).toList = sourceFields41 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag41 (logical : Nat → F) :
    ((sourceFields41 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics41 (logical : Nat → F) :
    (sourceLookup41).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields41 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions41.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values41]
    exact source_tag41 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions41 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values41 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values41 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand42 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 43)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 88))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 19))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1879048178, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 23))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 103))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 104))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 41⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions42 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 45]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 152])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 83])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 87])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 167])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 168])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup42 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions42⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields42 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 45]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 152])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 83])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1879048178, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 87])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 167])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 168])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values42 (logical : Nat → F) :
    (sourceExpressions42.map (Verification.environment logical)).toList = sourceFields42 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag42 (logical : Nat → F) :
    ((sourceFields42 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics42 (logical : Nat → F) :
    (sourceLookup42).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields42 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions42.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values42]
    exact source_tag42 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions42 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values42 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values42 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand43 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 105))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 12))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 109))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 110))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 42⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions43 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 169])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 76])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 173])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 174])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup43 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions43⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields43 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 169])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 76])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 173])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 174])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values43 (logical : Nat → F) :
    (sourceExpressions43.map (Verification.environment logical)).toList = sourceFields43 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag43 (logical : Nat → F) :
    ((sourceFields43 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics43 (logical : Nat → F) :
    (sourceLookup43).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields43 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions43.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values43]
    exact source_tag43 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions43 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values43 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values43 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand44 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 46)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 105))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 13))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 111))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 112))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 43⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions44 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 48]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 169])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 77])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 175])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 176])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup44 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions44⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields44 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 48]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 169])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 77])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 175])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 176])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values44 (logical : Nat → F) :
    (sourceExpressions44.map (Verification.environment logical)).toList = sourceFields44 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag44 (logical : Nat → F) :
    ((sourceFields44 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics44 (logical : Nat → F) :
    (sourceLookup44).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields44 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions44.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values44]
    exact source_tag44 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions44 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values44 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values44 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand45 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 106))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 14))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 113))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 114))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 44⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions45 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 170])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 78])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 177])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 178])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup45 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions45⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields45 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 170])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 78])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 177])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 178])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values45 (logical : Nat → F) :
    (sourceExpressions45.map (Verification.environment logical)).toList = sourceFields45 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag45 (logical : Nat → F) :
    ((sourceFields45 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics45 (logical : Nat → F) :
    (sourceLookup45).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields45 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions45.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values45]
    exact source_tag45 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions45 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values45 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values45 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand46 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 47)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 106))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 15))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 115))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 116))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 45⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions46 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 49]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 170])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 79])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 179])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 180])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup46 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions46⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields46 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 49]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 170])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 79])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 179])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 180])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values46 (logical : Nat → F) :
    (sourceExpressions46.map (Verification.environment logical)).toList = sourceFields46 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag46 (logical : Nat → F) :
    ((sourceFields46 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics46 (logical : Nat → F) :
    (sourceLookup46).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields46 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions46.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values46]
    exact source_tag46 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions46 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values46 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values46 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand47 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 107))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 16))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1342177270, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1610612724, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 117))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 118))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1476394885, by decide⟩⟩⟩], 46⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions47 : Vector (Airbender.Expression F) 9 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 171])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 80])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 181])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 182])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup47 : Lookup F := ⟨(WorkerConstraints.setupTable .thetaRho).toRaw, sourceExpressions47⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields47 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 171])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 80])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1342177270, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1610612724, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 181])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 182])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1476394885, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values47 (logical : Nat → F) :
    (sourceExpressions47.map (Verification.environment logical)).toList = sourceFields47 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag47 (logical : Nat → F) :
    ((sourceFields47 logical)[8]?).getD 0 ≠ 0 := by
  change (58 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics47 (logical : Nat → F) :
    (sourceLookup47).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields47 logical = NativeWorkerSetup.rows .thetaRho 0 index := by
  have tag : (((sourceExpressions47.map (Verification.environment logical)).toList)[width .thetaRho - 1]?).getD 0 ≠ 0 := by
    rw [source_values47]
    exact source_tag47 logical
  have equivalent := generic_lookup_refinement .thetaRho sourceExpressions47 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values47 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values47 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
