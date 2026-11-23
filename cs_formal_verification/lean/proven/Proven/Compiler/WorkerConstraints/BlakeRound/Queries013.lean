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
noncomputable def operand156 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 267))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 18)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 34)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 86)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 88)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 102)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 118)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 120)), (⟨⟨134217727, by decide⟩⟩, (.BaseLayerWitness 137)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 140)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 142)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 144)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 194)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 195)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 278)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 279)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 280))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 284))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 67⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions156 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 406])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 157]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 173]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 225]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 227]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 241]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 257]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 259]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 276]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 279]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 281]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 283]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 333]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 334]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 417]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 418]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 419])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 423])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup156 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions156⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields156 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 406])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 157]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 173]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 225]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 227]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 241]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 257]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 259]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 276]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 279]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 281]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 283]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 333]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 334]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 417]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 418]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 419])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 423])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values156 (logical : Nat → F) :
    (sourceExpressions156.map (Verification.environment logical)).toList = sourceFields156 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag156 (logical : Nat → F) :
    ((sourceFields156 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics156 (logical : Nat → F) :
    (sourceLookup156).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields156 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions156.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values156]
    exact source_tag156 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions156 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values156 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values156 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand157 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 292))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 286))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 295))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 68⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions157 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 431])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 425])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 434])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup157 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions157⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields157 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 431])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 425])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 434])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values157 (logical : Nat → F) :
    (sourceExpressions157.map (Verification.environment logical)).toList = sourceFields157 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag157 (logical : Nat → F) :
    ((sourceFields157 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics157 (logical : Nat → F) :
    (sourceLookup157).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields157 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions157.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values157]
    exact source_tag157 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions157 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values157 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values157 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand158 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 294))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 289))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 296))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 69⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions158 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 433])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 428])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 435])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup158 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions158⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields158 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 433])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 428])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 435])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values158 (logical : Nat → F) :
    (sourceExpressions158.map (Verification.environment logical)).toList = sourceFields158 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag158 (logical : Nat → F) :
    ((sourceFields158 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics158 (logical : Nat → F) :
    (sourceLookup158).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields158 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions158.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values158]
    exact source_tag158 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions158 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values158 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values158 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand159 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 193)), (⟨⟨536870912, by decide⟩⟩, (.BaseLayerWitness 196)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 291)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 292))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 293))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 51)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 205)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 206)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 209)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 225)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 228)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 230)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 283)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 284)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 285)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 286)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 287))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 288))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 297))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1207959431, by decide⟩⟩⟩], 70⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions159 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 332]), (.Product #[.Constant ⟨⟨536870912, by decide⟩⟩, .Var 335]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 430]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 431])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 432])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 190]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 344]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 345]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 348]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 364]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 367]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 369]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 422]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 423]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 424]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 425]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 426])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 427])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 436])]), Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup159 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions159⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields159 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 332]), (.Product #[.Constant ⟨⟨536870912, by decide⟩⟩, .Var 335]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 430]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 431])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 432])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 190]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 344]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 345]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 348]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 364]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 367]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 369]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 422]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 423]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 424]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 425]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 426])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 427])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 436])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values159 (logical : Nat → F) :
    (sourceExpressions159.map (Verification.environment logical)).toList = sourceFields159 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag159 (logical : Nat → F) :
    ((sourceFields159 logical)[5]?).getD 0 ≠ 0 := by
  change (57 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics159 (logical : Nat → F) :
    (sourceLookup159).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields159 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions159.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values159]
    exact source_tag159 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions159 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values159 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values159 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand160 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 194)), (⟨⟨536870912, by decide⟩⟩, (.BaseLayerWitness 195)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 293)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 294))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 291))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 52)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 203)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 204)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 209)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 212)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 226)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 227)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 230)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 232)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 281)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 282)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 287)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 288)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 289)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 290))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 285))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 298))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1207959431, by decide⟩⟩⟩], 71⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions160 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 333]), (.Product #[.Constant ⟨⟨536870912, by decide⟩⟩, .Var 334]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 432]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 433])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 430])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 191]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 342]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 343]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 348]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 351]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 365]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 366]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 369]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 371]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 420]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 421]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 426]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 427]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 428]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 429])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 424])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 437])]), Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup160 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions160⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields160 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 333]), (.Product #[.Constant ⟨⟨536870912, by decide⟩⟩, .Var 334]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 432]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 433])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 430])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 191]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 342]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 343]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 348]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 351]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 365]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 366]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 369]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 371]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 420]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 421]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 426]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 427]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 428]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 429])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 424])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 437])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values160 (logical : Nat → F) :
    (sourceExpressions160.map (Verification.environment logical)).toList = sourceFields160 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag160 (logical : Nat → F) :
    ((sourceFields160 logical)[5]?).getD 0 ≠ 0 := by
  change (57 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics160 (logical : Nat → F) :
    (sourceLookup160).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields160 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions160.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values160]
    exact source_tag160 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions160 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values160 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values160 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand161 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 284))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 56)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 299))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 301))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 72⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions161 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 423])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 39]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 438])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 440])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup161 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions161⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields161 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 423])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 39]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 438])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 440])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values161 (logical : Nat → F) :
    (sourceExpressions161.map (Verification.environment logical)).toList = sourceFields161 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag161 (logical : Nat → F) :
    ((sourceFields161 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics161 (logical : Nat → F) :
    (sourceLookup161).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields161 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions161.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values161]
    exact source_tag161 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions161 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values161 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values161 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand162 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 282))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 57)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 300))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 302))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 73⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions162 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 421])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 40]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 439])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 441])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup162 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions162⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields162 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 421])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 40]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 439])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 441])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values162 (logical : Nat → F) :
    (sourceExpressions162.map (Verification.environment logical)).toList = sourceFields162 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag162 (logical : Nat → F) :
    ((sourceFields162 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics162 (logical : Nat → F) :
    (sourceLookup162).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields162 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions162.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values162]
    exact source_tag162 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions162 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values162 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values162 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand163 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 283))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 299))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerMemory 56)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 16)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 32)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 85)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 87)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 101)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 103)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 118)), (⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 138)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 139)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 142)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 193)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 196)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 278)), (⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 296)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 297))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 147)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 302))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 74⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions163 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 422])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 438])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 39]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 155]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 171]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 224]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 226]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 240]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 242]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 257]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 277]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 278]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 281]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 332]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 335]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 417]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 435]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 436])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 100]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 441])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup163 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions163⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields163 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 422])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 438])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 39]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 155]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 171]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 224]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 226]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 240]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 242]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 257]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 277]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 278]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 281]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 332]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 335]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 417]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 435]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 436])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 100]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 441])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values163 (logical : Nat → F) :
    (sourceExpressions163.map (Verification.environment logical)).toList = sourceFields163 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag163 (logical : Nat → F) :
    ((sourceFields163 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics163 (logical : Nat → F) :
    (sourceLookup163).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields163 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions163.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values163]
    exact source_tag163 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions163 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values163 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values163 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand164 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 281))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 300))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨2013265920, by decide⟩⟩, (.BaseLayerMemory 56)), (⟨⟨2013200385, by decide⟩⟩, (.BaseLayerMemory 57)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 16)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 18)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 32)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 34)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 85)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 86)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 87)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 88)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 101)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 102)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 103)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 104)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 120)), (⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 137)), (⟨⟨128, by decide⟩⟩, (.BaseLayerWitness 138)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 139)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 140)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 144)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 193)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 194)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 195)), (⟨⟨512, by decide⟩⟩, (.BaseLayerWitness 196)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 280)), (⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 295)), (⟨⟨128, by decide⟩⟩, (.BaseLayerWitness 296)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 297)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 298))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 146)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 301))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 75⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions164 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 420])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 439])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013265920, by decide⟩⟩, .Var 39]), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 40]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 155]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 157]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 171]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 173]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 224]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 225]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 226]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 227]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 240]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 241]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 242]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 243]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 259]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 276]), (.Product #[.Constant ⟨⟨128, by decide⟩⟩, .Var 277]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 278]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 279]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 283]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 332]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 333]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 334]), (.Product #[.Constant ⟨⟨512, by decide⟩⟩, .Var 335]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 419]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 434]), (.Product #[.Constant ⟨⟨128, by decide⟩⟩, .Var 435]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 436]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 437])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 99]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 440])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup164 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions164⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields164 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 420])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 439])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013265920, by decide⟩⟩, .Var 39]), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 40]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 155]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 157]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 171]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 173]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 224]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 225]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 226]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 227]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 240]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 241]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 242]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 243]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 259]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 276]), (.Product #[.Constant ⟨⟨128, by decide⟩⟩, .Var 277]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 278]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 279]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 283]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 332]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 333]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 334]), (.Product #[.Constant ⟨⟨512, by decide⟩⟩, .Var 335]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 419]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 434]), (.Product #[.Constant ⟨⟨128, by decide⟩⟩, .Var 435]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 436]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 437])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 99]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 440])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values164 (logical : Nat → F) :
    (sourceExpressions164.map (Verification.environment logical)).toList = sourceFields164 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag164 (logical : Nat → F) :
    ((sourceFields164 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics164 (logical : Nat → F) :
    (sourceLookup164).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields164 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions164.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values164]
    exact source_tag164 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions164 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values164 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values164 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand165 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 296))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 116)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 303))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 305))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 76⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions165 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 435])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 79]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 442])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 444])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup165 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions165⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields165 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 435])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 79]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 442])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 444])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values165 (logical : Nat → F) :
    (sourceExpressions165.map (Verification.environment logical)).toList = sourceFields165 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag165 (logical : Nat → F) :
    ((sourceFields165 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics165 (logical : Nat → F) :
    (sourceLookup165).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields165 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions165.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values165]
    exact source_tag165 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions165 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values165 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values165 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand166 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 295))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 117)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 304))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 306))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 77⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions166 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 434])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 80]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 443])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 445])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup166 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions166⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields166 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 434])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 80]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 443])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 445])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values166 (logical : Nat → F) :
    (sourceExpressions166.map (Verification.environment logical)).toList = sourceFields166 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag166 (logical : Nat → F) :
    ((sourceFields166 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics166 (logical : Nat → F) :
    (sourceLookup166).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields166 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions166.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values166]
    exact source_tag166 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions166 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values166 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values166 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand167 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 297))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 303))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerMemory 116)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerMemory 146)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 51)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 205)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 206)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 209)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 225)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 228)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 230)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 283)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 284)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 287))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨8388608, by decide⟩⟩, (.BaseLayerMemory 87)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 306))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939523977, by decide⟩⟩⟩], 78⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions167 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 436])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 442])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 79]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 99]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 190]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 344]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 345]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 348]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 364]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 367]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 369]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 422]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 423]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 426])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 60]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 445])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939523977, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup167 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions167⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields167 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 436])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 442])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 79]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 99]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 190]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 344]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 345]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 348]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 364]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 367]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 369]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 422]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 423]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 426])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 60]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 445])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939523977, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values167 (logical : Nat → F) :
    (sourceExpressions167.map (Verification.environment logical)).toList = sourceFields167 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag167 (logical : Nat → F) :
    ((sourceFields167 logical)[5]?).getD 0 ≠ 0 := by
  change (56 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics167 (logical : Nat → F) :
    (sourceLookup167).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields167 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions167.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values167]
    exact source_tag167 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions167 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values167 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values167 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.BlakeRound
