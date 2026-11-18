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
noncomputable def operand36 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 5))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 17))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 29))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 41))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 53))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 65))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741688, by decide⟩⟩⟩], 7⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions36 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 52])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 64])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 76])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 100])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 112])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup36 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions36⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields36 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 52])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 64])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 76])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 100])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 112])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values36 (logical : Nat → F) :
    (sourceExpressions36.map (Verification.environment logical)).toList = sourceFields36 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag36 (logical : Nat → F) :
    ((sourceFields36 logical)[7]?).getD 0 ≠ 0 := by
  change (64 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics36 (logical : Nat → F) :
    (sourceLookup36).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields36 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions36.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values36]
    exact source_tag36 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions36 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values36 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values36 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand37 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 6))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 18))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 30))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 42))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 54))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 66))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741688, by decide⟩⟩⟩], 8⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions37 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 53])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 65])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 77])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 89])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 101])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 113])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup37 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions37⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields37 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 53])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 65])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 77])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 89])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 101])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 113])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values37 (logical : Nat → F) :
    (sourceExpressions37.map (Verification.environment logical)).toList = sourceFields37 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag37 (logical : Nat → F) :
    ((sourceFields37 logical)[7]?).getD 0 ≠ 0 := by
  change (64 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics37 (logical : Nat → F) :
    (sourceLookup37).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields37 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions37.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values37]
    exact source_tag37 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions37 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values37 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values37 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand38 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 15)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 4)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 5)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 6))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 25)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 16)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 17)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 18))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 34)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 28)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 29)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 30))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 43)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 40)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 41)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 42))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 52)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 52)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 53)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 54))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 64)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 64)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 65)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 66))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741688, by decide⟩⟩⟩], 9⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions38 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 17]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 51]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 52]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 53])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 23]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 63]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 64]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 65])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 27]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 75]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 76]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 77])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 31]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 88]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 89])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 35]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 99]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 100]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 101])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 41]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 111]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 112]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 113])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup38 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions38⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields38 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 17]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 51]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 52]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 53])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 23]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 63]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 64]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 65])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 27]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 75]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 76]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 77])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 31]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 88]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 89])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 35]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 99]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 100]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 101])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 41]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 111]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 112]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 113])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values38 (logical : Nat → F) :
    (sourceExpressions38.map (Verification.environment logical)).toList = sourceFields38 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag38 (logical : Nat → F) :
    ((sourceFields38 logical)[7]?).getD 0 ≠ 0 := by
  change (64 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics38 (logical : Nat → F) :
    (sourceLookup38).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields38 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions38.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values38]
    exact source_tag38 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions38 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values38 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values38 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand39 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 7))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 19))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 31))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 43))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 55))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 67))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741688, by decide⟩⟩⟩], 10⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions39 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 54])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 66])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 78])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 90])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 102])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 114])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup39 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions39⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields39 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 54])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 66])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 78])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 90])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 102])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 114])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values39 (logical : Nat → F) :
    (sourceExpressions39.map (Verification.environment logical)).toList = sourceFields39 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag39 (logical : Nat → F) :
    ((sourceFields39 logical)[7]?).getD 0 ≠ 0 := by
  change (64 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics39 (logical : Nat → F) :
    (sourceLookup39).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields39 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions39.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values39]
    exact source_tag39 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions39 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values39 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values39 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand40 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 8))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 20))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 32))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 44))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 56))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 68))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741688, by decide⟩⟩⟩], 11⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions40 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 55])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 67])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 79])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 91])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 103])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 115])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup40 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions40⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields40 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 55])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 67])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 79])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 91])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 103])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 115])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values40 (logical : Nat → F) :
    (sourceExpressions40.map (Verification.environment logical)).toList = sourceFields40 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag40 (logical : Nat → F) :
    ((sourceFields40 logical)[7]?).getD 0 ≠ 0 := by
  change (64 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics40 (logical : Nat → F) :
    (sourceLookup40).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields40 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions40.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values40]
    exact source_tag40 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions40 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values40 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values40 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand41 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 9))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 21))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 33))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 45))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 57))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 69))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741688, by decide⟩⟩⟩], 12⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions41 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 56])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 68])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 80])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 92])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 104])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 116])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup41 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions41⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields41 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 56])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 68])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 80])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 92])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 104])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 116])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values41 (logical : Nat → F) :
    (sourceExpressions41.map (Verification.environment logical)).toList = sourceFields41 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag41 (logical : Nat → F) :
    ((sourceFields41 logical)[7]?).getD 0 ≠ 0 := by
  change (64 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics41 (logical : Nat → F) :
    (sourceLookup41).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields41 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions41.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values41]
    exact source_tag41 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions41 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values41 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values41 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand42 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 16)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 7)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 8)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 9))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 26)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 19)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 21))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 35)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 31)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 32)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 33))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 44)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 43)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 44)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 45))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 53)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 55)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 56)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 57))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 65)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 67)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 68)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 69))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741688, by decide⟩⟩⟩], 13⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions42 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 18]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 54]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 55]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 56])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 24]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 66]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 67]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 68])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 28]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 78]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 79]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 80])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 32]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 90]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 91]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 92])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 36]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 102]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 103]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 104])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 42]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 114]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 115]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 116])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup42 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions42⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields42 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 18]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 54]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 55]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 56])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 24]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 66]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 67]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 68])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 28]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 78]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 79]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 80])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 32]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 90]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 91]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 92])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 36]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 102]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 103]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 104])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 42]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 114]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 115]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 116])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values42 (logical : Nat → F) :
    (sourceExpressions42.map (Verification.environment logical)).toList = sourceFields42 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag42 (logical : Nat → F) :
    ((sourceFields42 logical)[7]?).getD 0 ≠ 0 := by
  change (64 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics42 (logical : Nat → F) :
    (sourceLookup42).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields42 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions42.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values42]
    exact source_tag42 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions42 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values42 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values42 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand43 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 10))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 22))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 34))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 46))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 58))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 70))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741688, by decide⟩⟩⟩], 14⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions43 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 57])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 69])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 81])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 93])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 105])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 117])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup43 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions43⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields43 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 57])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 69])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 81])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 93])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 105])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 117])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values43 (logical : Nat → F) :
    (sourceExpressions43.map (Verification.environment logical)).toList = sourceFields43 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag43 (logical : Nat → F) :
    ((sourceFields43 logical)[7]?).getD 0 ≠ 0 := by
  change (64 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics43 (logical : Nat → F) :
    (sourceLookup43).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields43 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions43.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values43]
    exact source_tag43 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions43 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values43 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values43 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand44 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 11))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 23))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 35))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 47))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 59))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 71))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741688, by decide⟩⟩⟩], 15⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions44 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 58])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 70])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 82])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 94])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 106])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 118])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup44 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions44⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields44 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 58])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 70])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 82])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 94])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 106])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 118])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values44 (logical : Nat → F) :
    (sourceExpressions44.map (Verification.environment logical)).toList = sourceFields44 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag44 (logical : Nat → F) :
    ((sourceFields44 logical)[7]?).getD 0 ≠ 0 := by
  change (64 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics44 (logical : Nat → F) :
    (sourceLookup44).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields44 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions44.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values44]
    exact source_tag44 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions44 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values44 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values44 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand45 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 12))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 36))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 48))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 60))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 72))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741688, by decide⟩⟩⟩], 16⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions45 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 59])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 71])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 83])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 95])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 107])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 119])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup45 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions45⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields45 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 59])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 71])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 83])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 95])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 107])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 119])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values45 (logical : Nat → F) :
    (sourceExpressions45.map (Verification.environment logical)).toList = sourceFields45 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag45 (logical : Nat → F) :
    ((sourceFields45 logical)[7]?).getD 0 ≠ 0 := by
  change (64 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics45 (logical : Nat → F) :
    (sourceLookup45).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields45 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions45.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values45]
    exact source_tag45 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions45 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values45 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values45 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand46 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 21)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 10)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 11)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 12))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 30)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 39)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 34)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 35)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 36))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 48)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 46)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 47)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 48))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 57)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 58)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 59)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 60))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 70)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 70)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 71)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 72))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741688, by decide⟩⟩⟩], 17⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions46 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 21]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 57]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 58]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 59])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 25]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 69]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 70]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 71])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 29]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 81]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 82]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 83])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 33]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 93]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 94]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 95])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 37]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 105]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 106]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 107])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 45]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 117]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 118]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 119])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup46 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions46⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields46 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 21]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 57]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 58]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 59])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 25]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 69]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 70]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 71])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 29]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 81]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 82]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 83])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 33]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 93]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 94]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 95])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 37]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 105]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 106]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 107])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 45]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 117]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 118]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 119])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values46 (logical : Nat → F) :
    (sourceExpressions46.map (Verification.environment logical)).toList = sourceFields46 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag46 (logical : Nat → F) :
    ((sourceFields46 logical)[7]?).getD 0 ≠ 0 := by
  change (64 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics46 (logical : Nat → F) :
    (sourceLookup46).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields46 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions46.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values46]
    exact source_tag46 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions46 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values46 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values46 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand47 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 13))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 25))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 37))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 49))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 61))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 73))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741688, by decide⟩⟩⟩], 18⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions47 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 60])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 72])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 96])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 108])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 120])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup47 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions47⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields47 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 60])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 72])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 84])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 96])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 108])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 120])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values47 (logical : Nat → F) :
    (sourceExpressions47.map (Verification.environment logical)).toList = sourceFields47 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag47 (logical : Nat → F) :
    ((sourceFields47 logical)[7]?).getD 0 ≠ 0 := by
  change (64 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics47 (logical : Nat → F) :
    (sourceLookup47).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields47 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions47.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values47]
    exact source_tag47 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions47 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values47 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values47 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
