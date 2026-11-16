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
noncomputable def operand132 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 203))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 223))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 224))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 228))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 43⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions132 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 342])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 362])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 363])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 367])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup132 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions132⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields132 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 342])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 362])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 363])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 367])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values132 (logical : Nat → F) :
    (sourceExpressions132.map (Verification.environment logical)).toList = sourceFields132 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag132 (logical : Nat → F) :
    ((sourceFields132 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics132 (logical : Nat → F) :
    (sourceLookup132).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields132 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions132.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values132]
    exact source_tag132 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions132 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values132 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values132 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand133 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 218))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 51)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 205)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 206)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 209)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 225)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 228)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 229)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 230))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 233))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 44⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions133 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 357])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 190]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 344]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 345]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 348]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 364]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 367]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 368]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 369])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 372])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup133 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions133⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields133 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 357])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 190]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 344]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 345]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 348]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 364]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 367]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 368]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 369])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 372])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values133 (logical : Nat → F) :
    (sourceExpressions133.map (Verification.environment logical)).toList = sourceFields133 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag133 (logical : Nat → F) :
    ((sourceFields133 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics133 (logical : Nat → F) :
    (sourceLookup133).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields133 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions133.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values133]
    exact source_tag133 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions133 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values133 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values133 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand134 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 217))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 52)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 203)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 204)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 209)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 212)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 226)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 227)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 230)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 231)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 232))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 234))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 45⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions134 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 356])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 191]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 342]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 343]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 348]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 351]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 365]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 366]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 369]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 370]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 371])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 373])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup134 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions134⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields134 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 356])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 191]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 342]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 343]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 348]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 351]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 365]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 366]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 369]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 370]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 371])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 373])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values134 (logical : Nat → F) :
    (sourceExpressions134.map (Verification.environment logical)).toList = sourceFields134 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag134 (logical : Nat → F) :
    ((sourceFields134 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics134 (logical : Nat → F) :
    (sourceLookup134).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields134 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions134.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values134]
    exact source_tag134 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions134 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values134 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values134 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand135 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 219))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 229))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 235))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 46⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions135 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 358])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 368])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 374])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup135 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions135⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields135 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 358])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 368])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 374])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values135 (logical : Nat → F) :
    (sourceExpressions135.map (Verification.environment logical)).toList = sourceFields135 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag135 (logical : Nat → F) :
    ((sourceFields135 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics135 (logical : Nat → F) :
    (sourceLookup135).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields135 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions135.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values135]
    exact source_tag135 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions135 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values135 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values135 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand136 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 220))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 231))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 236))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 47⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions136 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 359])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 370])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 375])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup136 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions136⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields136 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 359])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 370])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 375])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values136 (logical : Nat → F) :
    (sourceExpressions136.map (Verification.environment logical)).toList = sourceFields136 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag136 (logical : Nat → F) :
    ((sourceFields136 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics136 (logical : Nat → F) :
    (sourceLookup136).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields136 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions136.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values136]
    exact source_tag136 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions136 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values136 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values136 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand137 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 241))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 237))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 238))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 243))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 48⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions137 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 380])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 376])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 377])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 382])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup137 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions137⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields137 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 380])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 376])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 377])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 382])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values137 (logical : Nat → F) :
    (sourceExpressions137.map (Verification.environment logical)).toList = sourceFields137 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag137 (logical : Nat → F) :
    ((sourceFields137 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics137 (logical : Nat → F) :
    (sourceLookup137).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields137 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions137.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values137]
    exact source_tag137 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions137 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values137 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values137 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand138 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 57)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 241))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 28)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 44)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 97)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 237)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 238))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 244))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 49⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions138 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 196]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 380])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 167]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 183]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 236]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 376]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 377])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 383])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup138 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions138⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields138 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 196]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 380])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 167]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 183]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 236]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 376]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 377])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 383])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values138 (logical : Nat → F) :
    (sourceExpressions138.map (Verification.environment logical)).toList = sourceFields138 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag138 (logical : Nat → F) :
    ((sourceFields138 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics138 (logical : Nat → F) :
    (sourceLookup138).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields138 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions138.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values138]
    exact source_tag138 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions138 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values138 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values138 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand139 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 242))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 239))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 240))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 245))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 50⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions139 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 381])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 378])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 379])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 384])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup139 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions139⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields139 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 381])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 378])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 379])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 384])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values139 (logical : Nat → F) :
    (sourceExpressions139.map (Verification.environment logical)).toList = sourceFields139 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag139 (logical : Nat → F) :
    ((sourceFields139 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics139 (logical : Nat → F) :
    (sourceLookup139).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields139 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions139.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values139]
    exact source_tag139 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions139 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values139 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values139 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand140 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 58)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 242))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 30)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 46)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 98)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 238)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 239)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 240))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 246))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 51⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions140 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 197]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 381])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 169]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 185]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 237]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 377]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 378]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 379])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 385])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup140 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions140⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields140 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 197]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 381])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 169]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 185]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 237]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 377]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 378]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 379])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 385])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values140 (logical : Nat → F) :
    (sourceExpressions140.map (Verification.environment logical)).toList = sourceFields140 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag140 (logical : Nat → F) :
    ((sourceFields140 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics140 (logical : Nat → F) :
    (sourceLookup140).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields140 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions140.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values140]
    exact source_tag140 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions140 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values140 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values140 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand141 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 254))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 248))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 257))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 52⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions141 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 393])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 387])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 396])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup141 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions141⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields141 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 393])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 387])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 396])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values141 (logical : Nat → F) :
    (sourceExpressions141.map (Verification.environment logical)).toList = sourceFields141 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag141 (logical : Nat → F) :
    ((sourceFields141 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics141 (logical : Nat → F) :
    (sourceLookup141).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields141 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions141.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values141]
    exact source_tag141 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions141 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values141 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values141 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand142 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 256))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 251))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 258))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 53⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions142 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 395])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 390])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 397])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup142 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions142⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields142 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 395])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 390])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 397])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values142 (logical : Nat → F) :
    (sourceExpressions142.map (Verification.environment logical)).toList = sourceFields142 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag142 (logical : Nat → F) :
    ((sourceFields142 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics142 (logical : Nat → F) :
    (sourceLookup142).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields142 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions142.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values142]
    exact source_tag142 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions142 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values142 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values142 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand143 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 44)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 253)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 254))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 255))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 53)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 245)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 246)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 247)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 248)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 249))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 250))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 259))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1207959431, by decide⟩⟩⟩], 54⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions143 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 183]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 392]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 393])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 394])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 192]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 384]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 385]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 386]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 387]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 388])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 389])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 398])]), Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup143 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions143⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields143 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 183]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 392]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 393])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 394])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 192]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 384]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 385]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 386]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 387]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 388])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 389])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 398])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values143 (logical : Nat → F) :
    (sourceExpressions143.map (Verification.environment logical)).toList = sourceFields143 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag143 (logical : Nat → F) :
    ((sourceFields143 logical)[5]?).getD 0 ≠ 0 := by
  change (57 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics143 (logical : Nat → F) :
    (sourceLookup143).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields143 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions143.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values143]
    exact source_tag143 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions143 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values143 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values143 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.BlakeRound
