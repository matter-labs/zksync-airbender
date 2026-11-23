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
noncomputable def operand120 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 180))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 191))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 196))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 31⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions120 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 319])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 330])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 335])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup120 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions120⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields120 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 319])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 330])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 335])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values120 (logical : Nat → F) :
    (sourceExpressions120.map (Verification.environment logical)).toList = sourceFields120 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag120 (logical : Nat → F) :
    ((sourceFields120 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics120 (logical : Nat → F) :
    (sourceLookup120).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields120 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions120.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values120]
    exact source_tag120 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions120 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values120 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values120 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand121 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 201))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 197))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 198))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 203))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 32⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions121 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 340])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 336])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 337])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 342])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup121 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions121⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields121 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 340])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 336])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 337])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 342])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values121 (logical : Nat → F) :
    (sourceExpressions121.map (Verification.environment logical)).toList = sourceFields121 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag121 (logical : Nat → F) :
    ((sourceFields121 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics121 (logical : Nat → F) :
    (sourceLookup121).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields121 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions121.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values121]
    exact source_tag121 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions121 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values121 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values121 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand122 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 61)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 201))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 24)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 40)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 93)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 197)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 198))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 204))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 33⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions122 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 200]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 340])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 163]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 179]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 232]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 336]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 337])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 343])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup122 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions122⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields122 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 200]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 340])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 163]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 179]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 232]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 336]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 337])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 343])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values122 (logical : Nat → F) :
    (sourceExpressions122.map (Verification.environment logical)).toList = sourceFields122 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag122 (logical : Nat → F) :
    ((sourceFields122 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics122 (logical : Nat → F) :
    (sourceLookup122).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields122 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions122.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values122]
    exact source_tag122 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions122 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values122 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values122 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand123 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 202))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 199))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 200))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 205))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 34⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions123 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 341])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 338])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 339])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 344])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup123 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions123⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields123 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 341])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 338])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 339])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 344])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values123 (logical : Nat → F) :
    (sourceExpressions123.map (Verification.environment logical)).toList = sourceFields123 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag123 (logical : Nat → F) :
    ((sourceFields123 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics123 (logical : Nat → F) :
    (sourceLookup123).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields123 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions123.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values123]
    exact source_tag123 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions123 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values123 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values123 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand124 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 62)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 202))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 26)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 42)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 94)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 198)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 199)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 200))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 206))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 35⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions124 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 201]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 341])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 165]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 181]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 233]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 337]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 338]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 339])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 345])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup124 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions124⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields124 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 201]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 341])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 165]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 181]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 233]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 337]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 338]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 339])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 345])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values124 (logical : Nat → F) :
    (sourceExpressions124.map (Verification.environment logical)).toList = sourceFields124 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag124 (logical : Nat → F) :
    ((sourceFields124 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics124 (logical : Nat → F) :
    (sourceLookup124).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields124 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions124.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values124]
    exact source_tag124 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions124 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values124 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values124 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand125 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 214))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 208))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 217))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 36⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions125 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 353])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 347])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 356])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup125 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions125⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields125 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 353])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 347])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 356])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values125 (logical : Nat → F) :
    (sourceExpressions125.map (Verification.environment logical)).toList = sourceFields125 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag125 (logical : Nat → F) :
    ((sourceFields125 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics125 (logical : Nat → F) :
    (sourceLookup125).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields125 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions125.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values125]
    exact source_tag125 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions125 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values125 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values125 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand126 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 216))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 211))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 218))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 37⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions126 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 355])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 350])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 357])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup126 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions126⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields126 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 355])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 350])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 357])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values126 (logical : Nat → F) :
    (sourceExpressions126.map (Verification.environment logical)).toList = sourceFields126 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag126 (logical : Nat → F) :
    ((sourceFields126 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics126 (logical : Nat → F) :
    (sourceLookup126).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields126 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions126.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values126]
    exact source_tag126 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions126 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values126 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values126 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand127 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 40)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 213)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 214))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 215))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 51)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 205)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 206)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 207)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 208)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 209))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 210))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 219))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1207959431, by decide⟩⟩⟩], 38⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions127 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 179]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 352]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 353])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 354])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 190]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 344]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 345]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 346]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 347]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 348])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 349])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 358])]), Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup127 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions127⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields127 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 179]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 352]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 353])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 354])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 190]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 344]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 345]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 346]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 347]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 348])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 349])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 358])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values127 (logical : Nat → F) :
    (sourceExpressions127.map (Verification.environment logical)).toList = sourceFields127 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag127 (logical : Nat → F) :
    ((sourceFields127 logical)[5]?).getD 0 ≠ 0 := by
  change (57 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics127 (logical : Nat → F) :
    (sourceLookup127).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields127 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions127.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values127]
    exact source_tag127 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions127 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values127 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values127 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand128 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 42)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 215)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 216))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 213))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 52)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 203)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 204)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 209)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 210)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 211)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 212))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 207))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 220))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1207959431, by decide⟩⟩⟩], 39⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions128 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 181]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 354]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 355])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 352])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 191]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 342]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 343]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 348]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 349]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 350]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 351])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 346])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 359])]), Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup128 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions128⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields128 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 181]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 354]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 355])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 352])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 191]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 342]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 343]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 348]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 349]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 350]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 351])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 346])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 359])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values128 (logical : Nat → F) :
    (sourceExpressions128.map (Verification.environment logical)).toList = sourceFields128 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag128 (logical : Nat → F) :
    ((sourceFields128 logical)[5]?).getD 0 ≠ 0 := by
  change (57 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics128 (logical : Nat → F) :
    (sourceLookup128).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields128 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions128.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values128]
    exact source_tag128 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions128 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values128 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values128 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand129 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 206))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 24)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 40)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 93)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 95)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 198)), (⟨⟨134217727, by decide⟩⟩, (.BaseLayerWitness 218)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 219)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 221)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 222))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 225))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 40⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions129 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 345])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 163]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 179]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 232]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 234]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 337]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 357]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 358]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 360]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 361])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 364])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup129 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions129⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields129 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 345])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 163]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 179]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 232]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 234]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 337]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 357]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 358]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 360]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 361])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 364])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values129 (logical : Nat → F) :
    (sourceExpressions129.map (Verification.environment logical)).toList = sourceFields129 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag129 (logical : Nat → F) :
    ((sourceFields129 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics129 (logical : Nat → F) :
    (sourceLookup129).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields129 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions129.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values129]
    exact source_tag129 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions129 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values129 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values129 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand130 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 204))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 26)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 42)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 94)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 96)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 198)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 200)), (⟨⟨134217727, by decide⟩⟩, (.BaseLayerWitness 217)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 220)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 222)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 223)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 224))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 226))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 41⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions130 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 343])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 165]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 181]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 233]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 235]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 337]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 339]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 356]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 359]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 361]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 362]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 363])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 365])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup130 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions130⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields130 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 343])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 165]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 181]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 233]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 235]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 337]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 339]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 356]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 359]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 361]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 362]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 363])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 365])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values130 (logical : Nat → F) :
    (sourceExpressions130.map (Verification.environment logical)).toList = sourceFields130 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag130 (logical : Nat → F) :
    ((sourceFields130 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics130 (logical : Nat → F) :
    (sourceLookup130).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields130 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions130.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values130]
    exact source_tag130 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions130 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values130 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values130 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand131 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 205))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 221))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 222))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 227))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 42⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions131 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 344])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 360])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 361])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 366])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup131 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions131⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields131 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 344])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 360])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 361])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 366])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values131 (logical : Nat → F) :
    (sourceExpressions131.map (Verification.environment logical)).toList = sourceFields131 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag131 (logical : Nat → F) :
    ((sourceFields131 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics131 (logical : Nat → F) :
    (sourceLookup131).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields131 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions131.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values131]
    exact source_tag131 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions131 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values131 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values131 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.BlakeRound
