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
noncomputable def operand252 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 128)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 331))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 447)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 448))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 450))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 163⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions252 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 470])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 586]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 587])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 589])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup252 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions252⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields252 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 470])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 586]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 587])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 589])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values252 (logical : Nat → F) :
    (sourceExpressions252.map (Verification.environment logical)).toList = sourceFields252 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag252 (logical : Nat → F) :
    ((sourceFields252 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics252 (logical : Nat → F) :
    (sourceLookup252).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields252 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions252.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values252]
    exact source_tag252 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions252 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values252 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values252 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand253 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 396))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 451))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 452))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 164⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions253 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 535])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 590])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 591])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup253 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions253⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields253 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 535])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 590])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 591])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values253 (logical : Nat → F) :
    (sourceExpressions253.map (Verification.environment logical)).toList = sourceFields253 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag253 (logical : Nat → F) :
    ((sourceFields253 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics253 (logical : Nat → F) :
    (sourceLookup253).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields253 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions253.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values253]
    exact source_tag253 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions253 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values253 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values253 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand254 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨8388608, by decide⟩⟩, (.BaseLayerMemory 81)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 396))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 33)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 451))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 453))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 165⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions254 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 56]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 535])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 172]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 590])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 592])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup254 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions254⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields254 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 56]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 535])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 172]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 590])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 592])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values254 (logical : Nat → F) :
    (sourceExpressions254.map (Verification.environment logical)).toList = sourceFields254 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag254 (logical : Nat → F) :
    ((sourceFields254 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics254 (logical : Nat → F) :
    (sourceLookup254).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields254 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions254.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values254]
    exact source_tag254 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions254 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values254 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values254 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand255 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 332))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 452)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 454))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 455))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 166⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions255 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 471])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 591]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 593])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 594])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup255 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions255⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields255 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 471])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 591]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 593])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 594])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values255 (logical : Nat → F) :
    (sourceExpressions255.map (Verification.environment logical)).toList = sourceFields255 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag255 (logical : Nat → F) :
    ((sourceFields255 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics255 (logical : Nat → F) :
    (sourceLookup255).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields255 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions255.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values255]
    exact source_tag255 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions255 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values255 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values255 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand256 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 129)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 332))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 453)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 454))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 456))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 167⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions256 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 88]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 471])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 592]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 593])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 595])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup256 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions256⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields256 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 88]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 471])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 592]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 593])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 595])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values256 (logical : Nat → F) :
    (sourceExpressions256.map (Verification.environment logical)).toList = sourceFields256 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag256 (logical : Nat → F) :
    ((sourceFields256 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics256 (logical : Nat → F) :
    (sourceLookup256).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields256 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions256.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values256]
    exact source_tag256 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions256 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values256 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values256 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand257 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 305))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 457))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 458))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 168⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions257 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 444])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 596])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 597])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup257 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions257⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields257 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 444])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 596])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 597])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values257 (logical : Nat → F) :
    (sourceExpressions257.map (Verification.environment logical)).toList = sourceFields257 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag257 (logical : Nat → F) :
    ((sourceFields257 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics257 (logical : Nat → F) :
    (sourceLookup257).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields257 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions257.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values257]
    exact source_tag257 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions257 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values257 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values257 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand258 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨8388608, by decide⟩⟩, (.BaseLayerMemory 86)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 305))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 35)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 457))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 459))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 169⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions258 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 59]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 444])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 174]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 596])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 598])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup258 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions258⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields258 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 59]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 444])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 174]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 596])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 598])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values258 (logical : Nat → F) :
    (sourceExpressions258.map (Verification.environment logical)).toList = sourceFields258 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag258 (logical : Nat → F) :
    ((sourceFields258 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics258 (logical : Nat → F) :
    (sourceLookup258).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields258 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions258.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values258]
    exact source_tag258 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions258 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values258 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values258 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand259 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 361))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 458)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 460))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 461))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 170⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions259 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 500])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 597]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 599])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 600])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup259 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions259⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields259 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 500])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 597]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 599])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 600])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values259 (logical : Nat → F) :
    (sourceExpressions259.map (Verification.environment logical)).toList = sourceFields259 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag259 (logical : Nat → F) :
    ((sourceFields259 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics259 (logical : Nat → F) :
    (sourceLookup259).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields259 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions259.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values259]
    exact source_tag259 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions259 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values259 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values259 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand260 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 134)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 361))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 459)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 460))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 462))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 171⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions260 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 91]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 500])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 598]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 599])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 601])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup260 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions260⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields260 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 91]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 500])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 598]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 599])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 601])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values260 (logical : Nat → F) :
    (sourceExpressions260.map (Verification.environment logical)).toList = sourceFields260 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag260 (logical : Nat → F) :
    ((sourceFields260 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics260 (logical : Nat → F) :
    (sourceLookup260).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields260 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions260.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values260]
    exact source_tag260 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions260 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values260 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values260 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand261 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 306))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 463))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 464))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 172⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions261 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 445])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 602])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 603])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup261 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions261⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields261 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 445])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 602])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 603])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values261 (logical : Nat → F) :
    (sourceExpressions261.map (Verification.environment logical)).toList = sourceFields261 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag261 (logical : Nat → F) :
    ((sourceFields261 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics261 (logical : Nat → F) :
    (sourceLookup261).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields261 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions261.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values261]
    exact source_tag261 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions261 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values261 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values261 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand262 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨8388608, by decide⟩⟩, (.BaseLayerMemory 87)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 306))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 37)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 463))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 465))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 173⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions262 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 60]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 445])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 176]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 602])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 604])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup262 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions262⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields262 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 60]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 445])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 176]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 602])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 604])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values262 (logical : Nat → F) :
    (sourceExpressions262.map (Verification.environment logical)).toList = sourceFields262 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag262 (logical : Nat → F) :
    ((sourceFields262 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics262 (logical : Nat → F) :
    (sourceLookup262).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields262 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions262.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values262]
    exact source_tag262 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions262 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values262 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values262 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand263 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 362))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 464)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 466))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 467))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 174⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions263 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 501])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 603]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 605])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 606])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup263 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions263⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields263 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 501])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 603]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 605])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 606])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values263 (logical : Nat → F) :
    (sourceExpressions263.map (Verification.environment logical)).toList = sourceFields263 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag263 (logical : Nat → F) :
    ((sourceFields263 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics263 (logical : Nat → F) :
    (sourceLookup263).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields263 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions263.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values263]
    exact source_tag263 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions263 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values263 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values263 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.BlakeRound
