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
noncomputable def operand204 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 227))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 30)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 46)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 98)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 100)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 114)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 154)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 155)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 238)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 240)), (⟨⟨134217727, by decide⟩⟩, (.BaseLayerWitness 257)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 260)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 262)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 264)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 368)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 369)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 370))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 374))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 115⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions204 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 366])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 169]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 185]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 237]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 239]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 253]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 293]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 294]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 377]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 379]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 396]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 399]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 401]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 403]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 507]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 508]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 509])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 513])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup204 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions204⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields204 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 366])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 169]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 185]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 237]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 239]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 253]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 293]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 294]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 377]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 379]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 396]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 399]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 401]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 403]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 507]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 508]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 509])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 513])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values204 (logical : Nat → F) :
    (sourceExpressions204.map (Verification.environment logical)).toList = sourceFields204 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag204 (logical : Nat → F) :
    ((sourceFields204 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics204 (logical : Nat → F) :
    (sourceLookup204).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields204 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions204.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values204]
    exact source_tag204 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions204 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values204 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values204 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand205 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 382))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 376))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 385))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 116⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions205 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 521])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 515])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 524])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup205 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions205⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields205 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 521])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 515])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 524])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values205 (logical : Nat → F) :
    (sourceExpressions205.map (Verification.environment logical)).toList = sourceFields205 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag205 (logical : Nat → F) :
    ((sourceFields205 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics205 (logical : Nat → F) :
    (sourceLookup205).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields205 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions205.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values205]
    exact source_tag205 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions205 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values205 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values205 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand206 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 384))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 379))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 386))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 117⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions206 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 523])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 518])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 525])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup206 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions206⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields206 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 523])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 518])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 525])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values206 (logical : Nat → F) :
    (sourceExpressions206.map (Verification.environment logical)).toList = sourceFields206 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag206 (logical : Nat → F) :
    ((sourceFields206 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics206 (logical : Nat → F) :
    (sourceLookup206).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields206 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions206.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values206]
    exact source_tag206 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions206 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values206 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values206 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand207 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 153)), (⟨⟨536870912, by decide⟩⟩, (.BaseLayerWitness 156)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 381)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 382))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 383))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 49)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 165)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 166)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 169)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 185)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 188)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 190)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 373)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 374)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 375)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 376)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 377))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 378))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 387))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1207959431, by decide⟩⟩⟩], 118⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions207 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 292]), (.Product #[.Constant ⟨⟨536870912, by decide⟩⟩, .Var 295]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 520]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 521])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 522])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 188]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 304]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 305]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 308]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 324]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 327]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 329]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 512]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 513]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 514]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 515]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 516])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 517])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 526])]), Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup207 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions207⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields207 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 292]), (.Product #[.Constant ⟨⟨536870912, by decide⟩⟩, .Var 295]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 520]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 521])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 522])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 188]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 304]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 305]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 308]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 324]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 327]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 329]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 512]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 513]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 514]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 515]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 516])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 517])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 526])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values207 (logical : Nat → F) :
    (sourceExpressions207.map (Verification.environment logical)).toList = sourceFields207 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag207 (logical : Nat → F) :
    ((sourceFields207 logical)[5]?).getD 0 ≠ 0 := by
  change (57 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics207 (logical : Nat → F) :
    (sourceLookup207).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields207 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions207.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values207]
    exact source_tag207 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions207 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values207 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values207 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand208 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 154)), (⟨⟨536870912, by decide⟩⟩, (.BaseLayerWitness 155)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 383)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 384))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 381))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 50)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 163)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 164)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 169)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 172)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 186)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 187)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 190)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 192)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 371)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 372)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 377)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 378)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 379)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 380))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 375))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 388))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1207959431, by decide⟩⟩⟩], 119⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions208 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 293]), (.Product #[.Constant ⟨⟨536870912, by decide⟩⟩, .Var 294]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 522]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 523])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 520])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 189]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 302]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 303]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 308]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 311]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 325]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 326]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 329]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 331]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 510]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 511]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 516]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 517]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 518]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 519])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 514])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 527])]), Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup208 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions208⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields208 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 293]), (.Product #[.Constant ⟨⟨536870912, by decide⟩⟩, .Var 294]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 522]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 523])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 520])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 189]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 302]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 303]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 308]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 311]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 325]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 326]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 329]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 331]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 510]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 511]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 516]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 517]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 518]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 519])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 514])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 527])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values208 (logical : Nat → F) :
    (sourceExpressions208.map (Verification.environment logical)).toList = sourceFields208 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag208 (logical : Nat → F) :
    ((sourceFields208 logical)[5]?).getD 0 ≠ 0 := by
  change (57 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics208 (logical : Nat → F) :
    (sourceLookup208).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields208 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions208.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values208]
    exact source_tag208 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions208 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values208 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values208 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand209 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 374))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 74)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 389))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 391))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 120⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions209 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 513])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 51]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 528])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 530])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup209 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions209⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields209 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 513])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 51]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 528])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 530])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values209 (logical : Nat → F) :
    (sourceExpressions209.map (Verification.environment logical)).toList = sourceFields209 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag209 (logical : Nat → F) :
    ((sourceFields209 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics209 (logical : Nat → F) :
    (sourceLookup209).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields209 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions209.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values209]
    exact source_tag209 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions209 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values209 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values209 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand210 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 372))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 75)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 390))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 392))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 121⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions210 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 511])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 52]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 529])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 531])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup210 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions210⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields210 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 511])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 52]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 529])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 531])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values210 (logical : Nat → F) :
    (sourceExpressions210.map (Verification.environment logical)).toList = sourceFields210 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag210 (logical : Nat → F) :
    ((sourceFields210 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics210 (logical : Nat → F) :
    (sourceLookup210).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields210 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions210.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values210]
    exact source_tag210 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions210 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values210 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values210 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand211 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 373))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 389))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerMemory 74)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 28)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 44)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 97)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 99)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 113)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 115)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 153)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 156)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 238)), (⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 258)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 259)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 262)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 368)), (⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 386)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 387))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 141)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 392))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 122⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions211 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 512])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 528])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 51]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 167]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 183]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 236]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 238]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 252]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 254]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 292]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 295]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 377]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 397]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 398]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 401]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 507]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 525]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 526])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 96]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 531])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup211 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions211⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields211 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 512])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 528])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 51]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 167]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 183]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 236]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 238]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 252]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 254]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 292]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 295]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 377]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 397]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 398]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 401]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 507]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 525]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 526])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 96]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 531])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values211 (logical : Nat → F) :
    (sourceExpressions211.map (Verification.environment logical)).toList = sourceFields211 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag211 (logical : Nat → F) :
    ((sourceFields211 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics211 (logical : Nat → F) :
    (sourceLookup211).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields211 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions211.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values211]
    exact source_tag211 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions211 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values211 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values211 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand212 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 371))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 390))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨2013265920, by decide⟩⟩, (.BaseLayerMemory 74)), (⟨⟨2013200385, by decide⟩⟩, (.BaseLayerMemory 75)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 28)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 30)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 44)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 46)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 97)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 98)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 99)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 100)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 113)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 114)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 115)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 116)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 153)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 154)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 155)), (⟨⟨512, by decide⟩⟩, (.BaseLayerWitness 156)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 240)), (⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 257)), (⟨⟨128, by decide⟩⟩, (.BaseLayerWitness 258)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 259)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 260)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 264)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 370)), (⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 385)), (⟨⟨128, by decide⟩⟩, (.BaseLayerWitness 386)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 387)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 388))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 140)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 391))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 123⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions212 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 510])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 529])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013265920, by decide⟩⟩, .Var 51]), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 52]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 167]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 169]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 183]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 185]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 236]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 237]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 238]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 239]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 252]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 253]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 254]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 255]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 292]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 293]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 294]), (.Product #[.Constant ⟨⟨512, by decide⟩⟩, .Var 295]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 379]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 396]), (.Product #[.Constant ⟨⟨128, by decide⟩⟩, .Var 397]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 398]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 399]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 403]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 509]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 524]), (.Product #[.Constant ⟨⟨128, by decide⟩⟩, .Var 525]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 526]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 527])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 95]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 530])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup212 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions212⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields212 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 510])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 529])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013265920, by decide⟩⟩, .Var 51]), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 52]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 167]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 169]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 183]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 185]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 236]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 237]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 238]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 239]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 252]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 253]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 254]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 255]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 292]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 293]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 294]), (.Product #[.Constant ⟨⟨512, by decide⟩⟩, .Var 295]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 379]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 396]), (.Product #[.Constant ⟨⟨128, by decide⟩⟩, .Var 397]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 398]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 399]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 403]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 509]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 524]), (.Product #[.Constant ⟨⟨128, by decide⟩⟩, .Var 525]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 526]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 527])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 95]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 530])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values212 (logical : Nat → F) :
    (sourceExpressions212.map (Verification.environment logical)).toList = sourceFields212 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag212 (logical : Nat → F) :
    ((sourceFields212 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics212 (logical : Nat → F) :
    (sourceLookup212).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields212 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions212.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values212]
    exact source_tag212 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions212 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values212 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values212 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand213 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 386))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 110)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 393))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 395))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 124⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions213 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 525])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 75]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 532])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 534])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup213 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions213⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields213 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 525])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 75]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 532])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 534])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values213 (logical : Nat → F) :
    (sourceExpressions213.map (Verification.environment logical)).toList = sourceFields213 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag213 (logical : Nat → F) :
    ((sourceFields213 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics213 (logical : Nat → F) :
    (sourceLookup213).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields213 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions213.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values213]
    exact source_tag213 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions213 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values213 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values213 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand214 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 385))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 111)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 394))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 396))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 125⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions214 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 524])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 76]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 533])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 535])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup214 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions214⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields214 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 524])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 76]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 533])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 535])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values214 (logical : Nat → F) :
    (sourceExpressions214.map (Verification.environment logical)).toList = sourceFields214 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag214 (logical : Nat → F) :
    ((sourceFields214 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics214 (logical : Nat → F) :
    (sourceLookup214).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields214 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions214.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values214]
    exact source_tag214 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions214 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values214 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values214 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand215 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 387))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 393))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerMemory 110)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerMemory 140)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 49)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 165)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 166)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 169)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 185)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 188)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 190)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 373)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 374)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 377))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨8388608, by decide⟩⟩, (.BaseLayerMemory 81)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 396))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939523977, by decide⟩⟩⟩], 126⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions215 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 526])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 532])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 75]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 95]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 188]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 304]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 305]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 308]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 324]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 327]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 329]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 512]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 513]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 516])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 56]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 535])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939523977, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup215 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions215⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields215 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 526])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 532])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 75]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 95]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 188]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 304]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 305]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 308]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 324]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 327]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 329]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 512]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 513]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 516])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 56]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 535])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939523977, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values215 (logical : Nat → F) :
    (sourceExpressions215.map (Verification.environment logical)).toList = sourceFields215 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag215 (logical : Nat → F) :
    ((sourceFields215 logical)[5]?).getD 0 ≠ 0 := by
  change (56 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics215 (logical : Nat → F) :
    (sourceLookup215).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields215 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions215.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values215]
    exact source_tag215 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions215 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values215 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values215 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.BlakeRound
