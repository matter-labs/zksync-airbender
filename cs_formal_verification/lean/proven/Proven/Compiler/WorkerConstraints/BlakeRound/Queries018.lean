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
noncomputable def operand216 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 388))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 394))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨2013265920, by decide⟩⟩, (.BaseLayerMemory 110)), (⟨⟨2013200385, by decide⟩⟩, (.BaseLayerMemory 111)), (⟨⟨1, by decide⟩⟩, (.BaseLayerMemory 140)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerMemory 141)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 49)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 50)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 163)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 164)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 165)), (⟨⟨256, by decide⟩⟩, (.BaseLayerWitness 166)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 172)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 185)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 186)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 187)), (⟨⟨256, by decide⟩⟩, (.BaseLayerWitness 188)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 192)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 371)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 372)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 373)), (⟨⟨256, by decide⟩⟩, (.BaseLayerWitness 374)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 380))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨8388608, by decide⟩⟩, (.BaseLayerMemory 80)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 395))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939523977, by decide⟩⟩⟩], 127⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions216 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 527])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 533])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013265920, by decide⟩⟩, .Var 75]), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 76]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 95]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 96]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 188]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 189]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 302]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 303]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 304]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 305]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 311]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 324]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 325]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 326]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 327]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 331]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 510]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 511]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 512]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 513]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 519])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 55]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 534])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939523977, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup216 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions216⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields216 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 527])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 533])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013265920, by decide⟩⟩, .Var 75]), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 76]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 95]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 96]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 188]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 189]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 302]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 303]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 304]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 305]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 311]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 324]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 325]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 326]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 327]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 331]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 510]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 511]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 512]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 513]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 519])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 55]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 534])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939523977, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values216 (logical : Nat → F) :
    (sourceExpressions216.map (Verification.environment logical)).toList = sourceFields216 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag216 (logical : Nat → F) :
    ((sourceFields216 logical)[5]?).getD 0 ≠ 0 := by
  change (56 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics216 (logical : Nat → F) :
    (sourceLookup216).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields216 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions216.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values216]
    exact source_tag216 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions216 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values216 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values216 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand217 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 397))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 363))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 398))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 128⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions217 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 536])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 502])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 537])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup217 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions217⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields217 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 536])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 502])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 537])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values217 (logical : Nat → F) :
    (sourceExpressions217.map (Verification.environment logical)).toList = sourceFields217 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag217 (logical : Nat → F) :
    ((sourceFields217 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics217 (logical : Nat → F) :
    (sourceLookup217).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields217 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions217.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values217]
    exact source_tag217 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions217 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values217 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values217 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand218 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 15)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 397))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 104)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 363))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 399))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 129⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions218 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 154]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 536])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 71]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 502])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 538])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup218 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions218⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields218 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 154]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 536])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 71]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 502])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 538])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values218 (logical : Nat → F) :
    (sourceExpressions218.map (Verification.environment logical)).toList = sourceFields218 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag218 (logical : Nat → F) :
    ((sourceFields218 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics218 (logical : Nat → F) :
    (sourceLookup218).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields218 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions218.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values218]
    exact source_tag218 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions218 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values218 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values218 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand219 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 398))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 299)), (⟨⟨1879048466, by decide⟩⟩, (.BaseLayerWitness 400))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 401))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 130⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions219 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 537])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 438]), (.Product #[.Constant ⟨⟨1879048466, by decide⟩⟩, .Var 539])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 540])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup219 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions219⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields219 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 537])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 438]), (.Product #[.Constant ⟨⟨1879048466, by decide⟩⟩, .Var 539])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 540])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values219 (logical : Nat → F) :
    (sourceExpressions219.map (Verification.environment logical)).toList = sourceFields219 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag219 (logical : Nat → F) :
    ((sourceFields219 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics219 (logical : Nat → F) :
    (sourceLookup219).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields219 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions219.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values219]
    exact source_tag219 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions219 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values219 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values219 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand220 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 399))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 56)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 299)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 400))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 402))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 131⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions220 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 538])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 39]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 438]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 539])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 541])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup220 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions220⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields220 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 538])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 39]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 438]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 539])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 541])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values220 (logical : Nat → F) :
    (sourceExpressions220.map (Verification.environment logical)).toList = sourceFields220 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag220 (logical : Nat → F) :
    ((sourceFields220 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics220 (logical : Nat → F) :
    (sourceLookup220).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields220 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions220.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values220]
    exact source_tag220 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions220 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values220 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values220 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand221 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 403))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 364))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 404))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 132⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions221 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 542])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 503])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 543])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup221 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions221⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields221 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 542])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 503])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 543])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values221 (logical : Nat → F) :
    (sourceExpressions221.map (Verification.environment logical)).toList = sourceFields221 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag221 (logical : Nat → F) :
    ((sourceFields221 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics221 (logical : Nat → F) :
    (sourceLookup221).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields221 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions221.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values221]
    exact source_tag221 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions221 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values221 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values221 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand222 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 17)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 403))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 105)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 364))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 405))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 133⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions222 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 156]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 542])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 72]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 503])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 544])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup222 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions222⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields222 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 156]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 542])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 72]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 503])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 544])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values222 (logical : Nat → F) :
    (sourceExpressions222.map (Verification.environment logical)).toList = sourceFields222 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag222 (logical : Nat → F) :
    ((sourceFields222 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics222 (logical : Nat → F) :
    (sourceLookup222).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields222 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions222.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values222]
    exact source_tag222 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions222 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values222 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values222 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand223 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 404))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 300)), (⟨⟨1879048466, by decide⟩⟩, (.BaseLayerWitness 406))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 407))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 134⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions223 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 543])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 439]), (.Product #[.Constant ⟨⟨1879048466, by decide⟩⟩, .Var 545])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 546])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup223 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions223⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields223 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 543])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 439]), (.Product #[.Constant ⟨⟨1879048466, by decide⟩⟩, .Var 545])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 546])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values223 (logical : Nat → F) :
    (sourceExpressions223.map (Verification.environment logical)).toList = sourceFields223 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag223 (logical : Nat → F) :
    ((sourceFields223 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics223 (logical : Nat → F) :
    (sourceLookup223).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields223 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions223.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values223]
    exact source_tag223 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions223 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values223 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values223 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand224 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 405))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 57)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 300)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 406))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 408))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 135⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions224 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 544])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 40]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 439]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 545])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 547])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup224 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions224⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields224 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 544])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 40]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 439]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 545])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 547])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values224 (logical : Nat → F) :
    (sourceExpressions224.map (Verification.environment logical)).toList = sourceFields224 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag224 (logical : Nat → F) :
    ((sourceFields224 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics224 (logical : Nat → F) :
    (sourceLookup224).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields224 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions224.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values224]
    exact source_tag224 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions224 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values224 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values224 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand225 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 409))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 393))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 410))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 136⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions225 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 548])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 532])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 549])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup225 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions225⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields225 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 548])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 532])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 549])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values225 (logical : Nat → F) :
    (sourceExpressions225.map (Verification.environment logical)).toList = sourceFields225 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag225 (logical : Nat → F) :
    ((sourceFields225 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics225 (logical : Nat → F) :
    (sourceLookup225).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields225 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions225.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values225]
    exact source_tag225 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions225 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values225 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values225 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand226 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 19)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 409))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 110)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 393))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 411))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 137⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions226 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 158]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 548])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 75]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 532])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 550])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup226 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions226⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields226 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 158]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 548])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 75]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 532])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 550])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values226 (logical : Nat → F) :
    (sourceExpressions226.map (Verification.environment logical)).toList = sourceFields226 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag226 (logical : Nat → F) :
    ((sourceFields226 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics226 (logical : Nat → F) :
    (sourceLookup226).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields226 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions226.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values226]
    exact source_tag226 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions226 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values226 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values226 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand227 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 410))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 329)), (⟨⟨1879048466, by decide⟩⟩, (.BaseLayerWitness 412))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 413))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 138⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions227 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 549])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 468]), (.Product #[.Constant ⟨⟨1879048466, by decide⟩⟩, .Var 551])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 552])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup227 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions227⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields227 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 549])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 468]), (.Product #[.Constant ⟨⟨1879048466, by decide⟩⟩, .Var 551])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 552])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values227 (logical : Nat → F) :
    (sourceExpressions227.map (Verification.environment logical)).toList = sourceFields227 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag227 (logical : Nat → F) :
    ((sourceFields227 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics227 (logical : Nat → F) :
    (sourceLookup227).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields227 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions227.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values227]
    exact source_tag227 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions227 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values227 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values227 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.BlakeRound
