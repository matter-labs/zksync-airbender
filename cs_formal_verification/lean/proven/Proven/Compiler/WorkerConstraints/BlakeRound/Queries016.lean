module
public import Proven.Compiler.WorkerConstraints.Values
public import Proven.Compiler.WorkerConstraints.Setup
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One actual resolved primitive operand. -/
noncomputable def operand192 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 274)), (⟨⟨536870912, by decide⟩⟩, (.BaseLayerWitness 275)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 353)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 354))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 351))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 48)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 123)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 124)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 129)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 132)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 146)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 147)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 150)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 152)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 341)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 342)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 347)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 348)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 349)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 350))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 345))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 358))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1207959431, by decide⟩⟩⟩], 103⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions192 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 413]), (.Product #[.Constant ⟨⟨536870912, by decide⟩⟩, .Var 414]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 492]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 493])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 490])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 187]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 262]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 263]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 268]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 271]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 285]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 286]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 289]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 291]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 480]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 481]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 486]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 487]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 488]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 489])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 484])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 497])]), Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup192 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions192⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields192 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 413]), (.Product #[.Constant ⟨⟨536870912, by decide⟩⟩, .Var 414]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 492]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 493])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 490])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 187]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 262]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 263]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 268]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 271]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 285]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 286]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 289]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 291]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 480]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 481]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 486]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 487]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 488]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 489])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 484])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 497])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values192 (logical : Nat → F) :
    (sourceExpressions192.map (Verification.environment logical)).toList = sourceFields192 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag192 (logical : Nat → F) :
    ((sourceFields192 logical)[5]?).getD 0 ≠ 0 := by
  change (57 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics192 (logical : Nat → F) :
    (sourceLookup192).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields192 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions192.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values192]
    exact source_tag192 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions192 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values192 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values192 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand193 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 344))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 68)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 359))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 361))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 104⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions193 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 483])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 47]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 498])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 500])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup193 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions193⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields193 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 483])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 47]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 498])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 500])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values193 (logical : Nat → F) :
    (sourceExpressions193.map (Verification.environment logical)).toList = sourceFields193 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag193 (logical : Nat → F) :
    ((sourceFields193 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics193 (logical : Nat → F) :
    (sourceLookup193).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields193 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions193.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values193]
    exact source_tag193 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions193 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values193 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values193 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand194 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 342))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 69)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 360))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 362))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 105⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions194 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 481])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 48]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 499])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 501])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup194 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions194⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields194 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 481])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 48]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 499])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 501])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values194 (logical : Nat → F) :
    (sourceExpressions194.map (Verification.environment logical)).toList = sourceFields194 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag194 (logical : Nat → F) :
    ((sourceFields194 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics194 (logical : Nat → F) :
    (sourceLookup194).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields194 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions194.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values194]
    exact source_tag194 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions194 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values194 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values194 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand195 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 343))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 359))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerMemory 68)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 24)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 40)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 93)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 95)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 109)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 111)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 198)), (⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 218)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 219)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 222)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 273)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 276)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 338)), (⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 356)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 357))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 135)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 362))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 106⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions195 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 482])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 498])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 47]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 163]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 179]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 232]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 234]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 248]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 250]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 337]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 357]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 358]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 361]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 412]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 415]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 477]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 495]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 496])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 92]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 501])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup195 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions195⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields195 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 482])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 498])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 47]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 163]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 179]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 232]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 234]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 248]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 250]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 337]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 357]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 358]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 361]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 412]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 415]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 477]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 495]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 496])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 92]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 501])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values195 (logical : Nat → F) :
    (sourceExpressions195.map (Verification.environment logical)).toList = sourceFields195 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag195 (logical : Nat → F) :
    ((sourceFields195 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics195 (logical : Nat → F) :
    (sourceLookup195).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields195 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions195.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values195]
    exact source_tag195 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions195 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values195 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values195 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand196 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 341))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 360))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨2013265920, by decide⟩⟩, (.BaseLayerMemory 68)), (⟨⟨2013200385, by decide⟩⟩, (.BaseLayerMemory 69)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 24)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 26)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 40)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 42)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 93)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 94)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 95)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 96)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 109)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 110)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 111)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 112)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 200)), (⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 217)), (⟨⟨128, by decide⟩⟩, (.BaseLayerWitness 218)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 219)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 220)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 224)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 273)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 274)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 275)), (⟨⟨512, by decide⟩⟩, (.BaseLayerWitness 276)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 340)), (⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 355)), (⟨⟨128, by decide⟩⟩, (.BaseLayerWitness 356)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 357)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 358))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 134)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 361))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 107⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions196 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 480])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 499])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013265920, by decide⟩⟩, .Var 47]), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 48]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 163]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 165]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 179]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 181]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 232]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 233]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 234]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 235]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 248]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 249]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 250]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 251]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 339]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 356]), (.Product #[.Constant ⟨⟨128, by decide⟩⟩, .Var 357]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 358]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 359]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 363]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 412]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 413]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 414]), (.Product #[.Constant ⟨⟨512, by decide⟩⟩, .Var 415]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 479]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 494]), (.Product #[.Constant ⟨⟨128, by decide⟩⟩, .Var 495]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 496]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 497])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 91]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 500])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup196 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions196⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields196 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 480])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 499])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013265920, by decide⟩⟩, .Var 47]), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 48]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 163]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 165]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 179]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 181]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 232]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 233]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 234]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 235]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 248]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 249]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 250]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 251]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 339]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 356]), (.Product #[.Constant ⟨⟨128, by decide⟩⟩, .Var 357]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 358]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 359]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 363]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 412]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 413]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 414]), (.Product #[.Constant ⟨⟨512, by decide⟩⟩, .Var 415]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 479]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 494]), (.Product #[.Constant ⟨⟨128, by decide⟩⟩, .Var 495]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 496]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 497])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 91]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 500])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values196 (logical : Nat → F) :
    (sourceExpressions196.map (Verification.environment logical)).toList = sourceFields196 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag196 (logical : Nat → F) :
    ((sourceFields196 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics196 (logical : Nat → F) :
    (sourceLookup196).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields196 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions196.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values196]
    exact source_tag196 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions196 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values196 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values196 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand197 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 356))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 104)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 363))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 365))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 108⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions197 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 495])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 71]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 502])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 504])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup197 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions197⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields197 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 495])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 71]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 502])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 504])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values197 (logical : Nat → F) :
    (sourceExpressions197.map (Verification.environment logical)).toList = sourceFields197 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag197 (logical : Nat → F) :
    ((sourceFields197 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics197 (logical : Nat → F) :
    (sourceLookup197).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields197 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions197.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values197]
    exact source_tag197 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions197 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values197 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values197 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand198 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 355))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 105)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 364))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 366))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 109⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions198 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 494])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 72]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 503])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 505])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup198 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions198⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields198 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 494])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 72]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 503])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 505])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values198 (logical : Nat → F) :
    (sourceExpressions198.map (Verification.environment logical)).toList = sourceFields198 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag198 (logical : Nat → F) :
    ((sourceFields198 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics198 (logical : Nat → F) :
    (sourceLookup198).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields198 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions198.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values198]
    exact source_tag198 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions198 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values198 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values198 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand199 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 357))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 363))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerMemory 104)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerMemory 134)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 47)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 125)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 126)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 129)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 145)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 148)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 150)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 343)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 344)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 347))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨8388608, by decide⟩⟩, (.BaseLayerMemory 99)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 366))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939523977, by decide⟩⟩⟩], 110⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions199 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 496])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 502])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 71]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 91]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 186]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 264]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 265]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 268]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 284]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 287]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 289]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 482]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 483]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 486])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 68]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 505])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939523977, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup199 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions199⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields199 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 496])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 502])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 71]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 91]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 186]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 264]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 265]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 268]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 284]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 287]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 289]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 482]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 483]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 486])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 68]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 505])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939523977, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values199 (logical : Nat → F) :
    (sourceExpressions199.map (Verification.environment logical)).toList = sourceFields199 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag199 (logical : Nat → F) :
    ((sourceFields199 logical)[5]?).getD 0 ≠ 0 := by
  change (56 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics199 (logical : Nat → F) :
    (sourceLookup199).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields199 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions199.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values199]
    exact source_tag199 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions199 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values199 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values199 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand200 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 358))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 364))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨2013265920, by decide⟩⟩, (.BaseLayerMemory 104)), (⟨⟨2013200385, by decide⟩⟩, (.BaseLayerMemory 105)), (⟨⟨1, by decide⟩⟩, (.BaseLayerMemory 134)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerMemory 135)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 47)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 48)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 123)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 124)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 125)), (⟨⟨256, by decide⟩⟩, (.BaseLayerWitness 126)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 132)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 145)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 146)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 147)), (⟨⟨256, by decide⟩⟩, (.BaseLayerWitness 148)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 152)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 341)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 342)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 343)), (⟨⟨256, by decide⟩⟩, (.BaseLayerWitness 344)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 350))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨8388608, by decide⟩⟩, (.BaseLayerMemory 98)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 365))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939523977, by decide⟩⟩⟩], 111⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions200 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 497])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 503])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013265920, by decide⟩⟩, .Var 71]), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 72]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 91]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 92]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 186]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 187]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 262]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 263]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 264]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 265]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 271]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 284]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 285]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 286]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 287]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 291]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 480]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 481]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 482]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 483]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 489])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 67]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 504])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939523977, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup200 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions200⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields200 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 497])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 503])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013265920, by decide⟩⟩, .Var 71]), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 72]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 91]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 92]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 186]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 187]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 262]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 263]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 264]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 265]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 271]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 284]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 285]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 286]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 287]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 291]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 480]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 481]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 482]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 483]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 489])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 67]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 504])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939523977, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values200 (logical : Nat → F) :
    (sourceExpressions200.map (Verification.environment logical)).toList = sourceFields200 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag200 (logical : Nat → F) :
    ((sourceFields200 logical)[5]?).getD 0 ≠ 0 := by
  change (56 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics200 (logical : Nat → F) :
    (sourceLookup200).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields200 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions200.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values200]
    exact source_tag200 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions200 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values200 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values200 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand201 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 225))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 367))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 368))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 371))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 112⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions201 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 364])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 506])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 507])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 510])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup201 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions201⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields201 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 364])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 506])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 507])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 510])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values201 (logical : Nat → F) :
    (sourceExpressions201.map (Verification.environment logical)).toList = sourceFields201 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag201 (logical : Nat → F) :
    ((sourceFields201 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics201 (logical : Nat → F) :
    (sourceLookup201).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields201 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions201.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values201]
    exact source_tag201 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions201 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values201 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values201 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand202 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 228))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 28)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 44)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 97)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 99)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 113)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 153)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 156)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 238)), (⟨⟨134217727, by decide⟩⟩, (.BaseLayerWitness 258)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 259)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 262)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 367)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 368))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 372))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 113⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions202 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 367])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 167]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 183]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 236]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 238]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 252]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 292]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 295]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 377]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 397]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 398]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 401]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 506]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 507])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 511])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup202 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions202⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields202 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 367])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 167]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 183]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 236]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 238]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 252]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 292]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 295]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 377]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 397]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 398]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 401]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 506]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 507])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 511])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values202 (logical : Nat → F) :
    (sourceExpressions202.map (Verification.environment logical)).toList = sourceFields202 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag202 (logical : Nat → F) :
    ((sourceFields202 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics202 (logical : Nat → F) :
    (sourceLookup202).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields202 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions202.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values202]
    exact source_tag202 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions202 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values202 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values202 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand203 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 226))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 369))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 370))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 373))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 114⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions203 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 365])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 508])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 509])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 512])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup203 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions203⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields203 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 365])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 508])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 509])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 512])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values203 (logical : Nat → F) :
    (sourceExpressions203.map (Verification.environment logical)).toList = sourceFields203 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag203 (logical : Nat → F) :
    ((sourceFields203 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics203 (logical : Nat → F) :
    (sourceLookup203).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields203 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions203.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values203]
    exact source_tag203 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions203 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values203 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values203 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.BlakeRound
