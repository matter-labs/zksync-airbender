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
noncomputable def operand228 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 411))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 62)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 329)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 412))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 414))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 139⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions228 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 550])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 43]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 468]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 551])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 553])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup228 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions228⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields228 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 550])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 43]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 468]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 551])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 553])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values228 (logical : Nat → F) :
    (sourceExpressions228.map (Verification.environment logical)).toList = sourceFields228 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag228 (logical : Nat → F) :
    ((sourceFields228 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics228 (logical : Nat → F) :
    (sourceLookup228).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields228 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions228.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values228]
    exact source_tag228 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions228 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values228 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values228 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand229 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 415))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 394))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 416))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 140⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions229 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 554])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 533])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 555])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup229 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions229⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields229 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 554])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 533])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 555])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values229 (logical : Nat → F) :
    (sourceExpressions229.map (Verification.environment logical)).toList = sourceFields229 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag229 (logical : Nat → F) :
    ((sourceFields229 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics229 (logical : Nat → F) :
    (sourceLookup229).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields229 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions229.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values229]
    exact source_tag229 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions229 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values229 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values229 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand230 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 21)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 415))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 111)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 394))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 417))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 141⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions230 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 160]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 554])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 76]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 533])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 556])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup230 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions230⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields230 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 160]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 554])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 76]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 533])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 556])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values230 (logical : Nat → F) :
    (sourceExpressions230.map (Verification.environment logical)).toList = sourceFields230 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag230 (logical : Nat → F) :
    ((sourceFields230 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics230 (logical : Nat → F) :
    (sourceLookup230).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields230 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions230.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values230]
    exact source_tag230 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions230 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values230 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values230 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand231 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 416))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 330)), (⟨⟨1879048466, by decide⟩⟩, (.BaseLayerWitness 418))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 419))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 142⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions231 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 555])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 469]), (.Product #[.Constant ⟨⟨1879048466, by decide⟩⟩, .Var 557])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 558])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup231 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions231⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields231 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 555])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 469]), (.Product #[.Constant ⟨⟨1879048466, by decide⟩⟩, .Var 557])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 558])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values231 (logical : Nat → F) :
    (sourceExpressions231.map (Verification.environment logical)).toList = sourceFields231 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag231 (logical : Nat → F) :
    ((sourceFields231 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics231 (logical : Nat → F) :
    (sourceLookup231).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields231 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions231.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values231]
    exact source_tag231 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions231 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values231 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values231 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand232 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 417))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 63)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 330)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 418))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 420))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 143⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions232 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 556])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 44]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 469]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 557])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 559])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup232 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions232⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields232 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 556])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 44]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 469]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 557])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 559])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values232 (logical : Nat → F) :
    (sourceExpressions232.map (Verification.environment logical)).toList = sourceFields232 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag232 (logical : Nat → F) :
    ((sourceFields232 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics232 (logical : Nat → F) :
    (sourceLookup232).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields232 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions232.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values232]
    exact source_tag232 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions232 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values232 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values232 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand233 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 421))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 303))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 422))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 144⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions233 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 560])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 442])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 561])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup233 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions233⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields233 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 560])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 442])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 561])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values233 (logical : Nat → F) :
    (sourceExpressions233.map (Verification.environment logical)).toList = sourceFields233 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag233 (logical : Nat → F) :
    ((sourceFields233 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics233 (logical : Nat → F) :
    (sourceLookup233).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields233 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions233.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values233]
    exact source_tag233 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions233 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values233 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values233 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand234 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 421))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 116)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 303))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 423))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 145⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions234 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 162]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 560])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 79]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 442])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 562])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup234 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions234⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields234 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 162]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 560])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 79]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 442])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 562])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values234 (logical : Nat → F) :
    (sourceExpressions234.map (Verification.environment logical)).toList = sourceFields234 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag234 (logical : Nat → F) :
    ((sourceFields234 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics234 (logical : Nat → F) :
    (sourceLookup234).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields234 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions234.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values234]
    exact source_tag234 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions234 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values234 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values234 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand235 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 422))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 359)), (⟨⟨1879048466, by decide⟩⟩, (.BaseLayerWitness 424))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 425))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 146⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions235 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 561])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 498]), (.Product #[.Constant ⟨⟨1879048466, by decide⟩⟩, .Var 563])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 564])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup235 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions235⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields235 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 561])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 498]), (.Product #[.Constant ⟨⟨1879048466, by decide⟩⟩, .Var 563])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 564])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values235 (logical : Nat → F) :
    (sourceExpressions235.map (Verification.environment logical)).toList = sourceFields235 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag235 (logical : Nat → F) :
    ((sourceFields235 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics235 (logical : Nat → F) :
    (sourceLookup235).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields235 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions235.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values235]
    exact source_tag235 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions235 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values235 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values235 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand236 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 423))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 68)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 359)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 424))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 426))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 147⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions236 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 562])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 47]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 498]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 563])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 565])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup236 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions236⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields236 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 562])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 47]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 498]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 563])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 565])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values236 (logical : Nat → F) :
    (sourceExpressions236.map (Verification.environment logical)).toList = sourceFields236 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag236 (logical : Nat → F) :
    ((sourceFields236 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics236 (logical : Nat → F) :
    (sourceLookup236).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields236 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions236.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values236]
    exact source_tag236 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions236 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values236 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values236 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand237 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 427))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 304))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 428))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 148⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions237 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 566])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 443])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 567])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup237 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions237⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields237 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 566])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 443])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 567])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values237 (logical : Nat → F) :
    (sourceExpressions237.map (Verification.environment logical)).toList = sourceFields237 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag237 (logical : Nat → F) :
    ((sourceFields237 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics237 (logical : Nat → F) :
    (sourceLookup237).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields237 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions237.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values237]
    exact source_tag237 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions237 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values237 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values237 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand238 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 25)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 427))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 117)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 304))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 429))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 149⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions238 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 164]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 566])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 80]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 443])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 568])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup238 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions238⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields238 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 164]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 566])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 80]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 443])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 568])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values238 (logical : Nat → F) :
    (sourceExpressions238.map (Verification.environment logical)).toList = sourceFields238 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag238 (logical : Nat → F) :
    ((sourceFields238 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics238 (logical : Nat → F) :
    (sourceLookup238).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields238 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions238.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values238]
    exact source_tag238 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions238 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values238 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values238 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand239 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 428))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 360)), (⟨⟨1879048466, by decide⟩⟩, (.BaseLayerWitness 430))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 431))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 150⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions239 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 567])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 499]), (.Product #[.Constant ⟨⟨1879048466, by decide⟩⟩, .Var 569])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 570])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup239 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions239⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields239 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 567])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 499]), (.Product #[.Constant ⟨⟨1879048466, by decide⟩⟩, .Var 569])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 570])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values239 (logical : Nat → F) :
    (sourceExpressions239.map (Verification.environment logical)).toList = sourceFields239 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag239 (logical : Nat → F) :
    ((sourceFields239 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics239 (logical : Nat → F) :
    (sourceLookup239).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields239 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions239.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values239]
    exact source_tag239 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions239 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values239 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values239 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.BlakeRound
