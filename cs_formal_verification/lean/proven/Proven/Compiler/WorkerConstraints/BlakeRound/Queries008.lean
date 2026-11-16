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
noncomputable def operand96 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 34)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 135)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 136))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 133))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 48)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 123)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 124)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 129)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 130)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 131)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 132))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 127))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 140))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1207959431, by decide⟩⟩⟩], 7⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions96 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 173]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 274]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 275])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 272])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 187]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 262]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 263]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 268]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 269]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 270]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 271])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 266])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 279])]), Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup96 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions96⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields96 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 173]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 274]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 275])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 272])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 187]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 262]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 263]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 268]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 269]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 270]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 271])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 266])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 279])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values96 (logical : Nat → F) :
    (sourceExpressions96.map (Verification.environment logical)).toList = sourceFields96 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag96 (logical : Nat → F) :
    ((sourceFields96 logical)[5]?).getD 0 ≠ 0 := by
  change (57 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics96 (logical : Nat → F) :
    (sourceLookup96).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields96 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions96.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values96]
    exact source_tag96 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions96 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values96 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values96 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand97 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 126))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 16)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 32)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 85)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 87)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 118)), (⟨⟨134217727, by decide⟩⟩, (.BaseLayerWitness 138)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 139)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 141)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 142))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 145))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 8⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions97 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 265])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 155]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 171]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 224]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 226]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 257]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 277]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 278]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 280]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 281])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 284])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup97 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions97⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields97 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 265])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 155]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 171]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 224]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 226]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 257]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 277]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 278]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 280]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 281])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 284])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values97 (logical : Nat → F) :
    (sourceExpressions97.map (Verification.environment logical)).toList = sourceFields97 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag97 (logical : Nat → F) :
    ((sourceFields97 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics97 (logical : Nat → F) :
    (sourceLookup97).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields97 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions97.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values97]
    exact source_tag97 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions97 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values97 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values97 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand98 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 124))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 18)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 34)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 86)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 88)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 118)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 120)), (⟨⟨134217727, by decide⟩⟩, (.BaseLayerWitness 137)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 140)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 142)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 143)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 144))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 146))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 9⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions98 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 263])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 157]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 173]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 225]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 227]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 257]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 259]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 276]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 279]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 281]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 282]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 283])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 285])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup98 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions98⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields98 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 263])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 157]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 173]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 225]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 227]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 257]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 259]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 276]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 279]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 281]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 282]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 283])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 285])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values98 (logical : Nat → F) :
    (sourceExpressions98.map (Verification.environment logical)).toList = sourceFields98 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag98 (logical : Nat → F) :
    ((sourceFields98 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics98 (logical : Nat → F) :
    (sourceLookup98).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields98 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions98.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values98]
    exact source_tag98 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions98 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values98 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values98 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand99 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 125))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 141))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 142))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 147))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 10⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions99 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 264])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 280])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 281])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 286])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup99 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions99⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields99 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 264])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 280])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 281])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 286])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values99 (logical : Nat → F) :
    (sourceExpressions99.map (Verification.environment logical)).toList = sourceFields99 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag99 (logical : Nat → F) :
    ((sourceFields99 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics99 (logical : Nat → F) :
    (sourceLookup99).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields99 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions99.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values99]
    exact source_tag99 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions99 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values99 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values99 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand100 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 123))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 143))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 144))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 148))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 11⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions100 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 262])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 282])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 283])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 287])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup100 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions100⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields100 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 262])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 282])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 283])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 287])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values100 (logical : Nat → F) :
    (sourceExpressions100.map (Verification.environment logical)).toList = sourceFields100 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag100 (logical : Nat → F) :
    ((sourceFields100 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics100 (logical : Nat → F) :
    (sourceLookup100).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields100 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions100.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values100]
    exact source_tag100 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions100 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values100 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values100 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand101 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 138))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 47)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 125)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 126)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 129)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 145)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 148)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 149)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 150))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 153))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 12⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions101 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 277])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 186]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 264]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 265]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 268]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 284]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 287]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 288]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 289])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 292])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup101 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions101⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields101 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 277])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 186]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 264]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 265]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 268]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 284]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 287]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 288]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 289])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 292])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values101 (logical : Nat → F) :
    (sourceExpressions101.map (Verification.environment logical)).toList = sourceFields101 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag101 (logical : Nat → F) :
    ((sourceFields101 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics101 (logical : Nat → F) :
    (sourceLookup101).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields101 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions101.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values101]
    exact source_tag101 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions101 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values101 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values101 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand102 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 137))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 48)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 123)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 124)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 129)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 132)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 146)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 147)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 150)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 151)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 152))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 154))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 13⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions102 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 276])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 187]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 262]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 263]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 268]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 271]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 285]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 286]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 289]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 290]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 291])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 293])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup102 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions102⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields102 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 276])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 187]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 262]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 263]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 268]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 271]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 285]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 286]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 289]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 290]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 291])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 293])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values102 (logical : Nat → F) :
    (sourceExpressions102.map (Verification.environment logical)).toList = sourceFields102 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag102 (logical : Nat → F) :
    ((sourceFields102 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics102 (logical : Nat → F) :
    (sourceLookup102).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields102 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions102.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values102]
    exact source_tag102 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions102 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values102 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values102 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand103 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 139))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 149))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 155))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 14⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions103 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 278])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 288])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 294])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup103 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions103⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields103 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 278])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 288])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 294])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values103 (logical : Nat → F) :
    (sourceExpressions103.map (Verification.environment logical)).toList = sourceFields103 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag103 (logical : Nat → F) :
    ((sourceFields103 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics103 (logical : Nat → F) :
    (sourceLookup103).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields103 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions103.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values103]
    exact source_tag103 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions103 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values103 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values103 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand104 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 140))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 151))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 156))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 15⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions104 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 279])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 290])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 295])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup104 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions104⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields104 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 279])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 290])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 295])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values104 (logical : Nat → F) :
    (sourceExpressions104.map (Verification.environment logical)).toList = sourceFields104 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag104 (logical : Nat → F) :
    ((sourceFields104 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics104 (logical : Nat → F) :
    (sourceLookup104).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields104 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions104.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values104]
    exact source_tag104 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions104 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values104 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values104 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand105 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 161))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 157))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 158))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 163))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 16⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions105 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 300])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 296])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 297])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 302])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup105 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions105⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields105 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 300])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 296])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 297])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 302])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values105 (logical : Nat → F) :
    (sourceExpressions105.map (Verification.environment logical)).toList = sourceFields105 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag105 (logical : Nat → F) :
    ((sourceFields105 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics105 (logical : Nat → F) :
    (sourceLookup105).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields105 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions105.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values105]
    exact source_tag105 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions105 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values105 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values105 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand106 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 55)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 161))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 36)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 89)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 157)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 158))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 164))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 17⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions106 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 194]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 300])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 159]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 175]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 228]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 296]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 297])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 303])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup106 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions106⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields106 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 194]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 300])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 159]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 175]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 228]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 296]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 297])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 303])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values106 (logical : Nat → F) :
    (sourceExpressions106.map (Verification.environment logical)).toList = sourceFields106 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag106 (logical : Nat → F) :
    ((sourceFields106 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics106 (logical : Nat → F) :
    (sourceLookup106).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields106 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions106.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values106]
    exact source_tag106 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions106 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values106 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values106 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand107 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 162))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 159))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 160))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 165))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 18⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions107 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 301])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 298])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 299])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 304])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup107 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions107⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields107 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 301])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 298])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 299])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 304])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values107 (logical : Nat → F) :
    (sourceExpressions107.map (Verification.environment logical)).toList = sourceFields107 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag107 (logical : Nat → F) :
    ((sourceFields107 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics107 (logical : Nat → F) :
    (sourceLookup107).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields107 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions107.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values107]
    exact source_tag107 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions107 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values107 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values107 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.BlakeRound
