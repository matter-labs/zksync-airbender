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
noncomputable def operand144 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 46)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 255)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 256))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 253))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 54)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 243)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 244)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 249)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 250)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 251)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 252))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 247))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 260))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1207959431, by decide⟩⟩⟩], 55⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions144 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 185]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 394]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 395])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 392])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 193]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 382]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 383]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 388]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 389]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 390]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 391])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 386])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 399])]), Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup144 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions144⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields144 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 185]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 394]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 395])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 392])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 193]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 382]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 383]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 388]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 389]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 390]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 391])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 386])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 399])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values144 (logical : Nat → F) :
    (sourceExpressions144.map (Verification.environment logical)).toList = sourceFields144 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag144 (logical : Nat → F) :
    ((sourceFields144 logical)[5]?).getD 0 ≠ 0 := by
  change (57 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics144 (logical : Nat → F) :
    (sourceLookup144).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields144 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions144.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values144]
    exact source_tag144 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions144 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values144 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values144 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand145 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 246))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 28)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 44)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 97)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 99)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 238)), (⟨⟨134217727, by decide⟩⟩, (.BaseLayerWitness 258)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 259)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 261)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 262))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 265))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 56⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions145 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 385])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 167]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 183]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 236]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 238]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 377]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 397]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 398]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 400]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 401])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 404])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup145 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions145⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields145 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 385])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 167]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 183]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 236]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 238]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 377]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 397]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 398]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 400]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 401])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 404])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values145 (logical : Nat → F) :
    (sourceExpressions145.map (Verification.environment logical)).toList = sourceFields145 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag145 (logical : Nat → F) :
    ((sourceFields145 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics145 (logical : Nat → F) :
    (sourceLookup145).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields145 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions145.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values145]
    exact source_tag145 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions145 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values145 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values145 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand146 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 244))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 30)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 46)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 98)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 100)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 238)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 240)), (⟨⟨134217727, by decide⟩⟩, (.BaseLayerWitness 257)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 260)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 262)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 263)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 264))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 266))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 57⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions146 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 383])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 169]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 185]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 237]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 239]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 377]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 379]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 396]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 399]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 401]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 402]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 403])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 405])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup146 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions146⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields146 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 383])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 169]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 185]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 237]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 239]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 377]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 379]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 396]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 399]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 401]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 402]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 403])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 405])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values146 (logical : Nat → F) :
    (sourceExpressions146.map (Verification.environment logical)).toList = sourceFields146 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag146 (logical : Nat → F) :
    ((sourceFields146 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics146 (logical : Nat → F) :
    (sourceLookup146).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields146 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions146.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values146]
    exact source_tag146 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions146 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values146 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values146 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand147 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 245))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 261))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 262))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 267))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 58⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions147 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 384])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 400])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 401])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 406])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup147 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions147⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields147 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 384])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 400])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 401])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 406])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values147 (logical : Nat → F) :
    (sourceExpressions147.map (Verification.environment logical)).toList = sourceFields147 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag147 (logical : Nat → F) :
    ((sourceFields147 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics147 (logical : Nat → F) :
    (sourceLookup147).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields147 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions147.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values147]
    exact source_tag147 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions147 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values147 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values147 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand148 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 243))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 263))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 264))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 268))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 59⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions148 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 382])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 402])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 403])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 407])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup148 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions148⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields148 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 382])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 402])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 403])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 407])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values148 (logical : Nat → F) :
    (sourceExpressions148.map (Verification.environment logical)).toList = sourceFields148 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag148 (logical : Nat → F) :
    ((sourceFields148 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics148 (logical : Nat → F) :
    (sourceLookup148).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields148 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions148.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values148]
    exact source_tag148 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions148 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values148 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values148 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand149 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 258))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 53)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 245)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 246)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 249)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 265)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 268)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 269)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 270))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 273))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 60⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions149 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 397])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 192]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 384]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 385]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 388]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 404]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 407]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 408]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 409])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 412])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup149 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions149⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields149 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 397])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 192]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 384]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 385]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 388]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 404]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 407]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 408]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 409])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 412])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values149 (logical : Nat → F) :
    (sourceExpressions149.map (Verification.environment logical)).toList = sourceFields149 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag149 (logical : Nat → F) :
    ((sourceFields149 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics149 (logical : Nat → F) :
    (sourceLookup149).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields149 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions149.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values149]
    exact source_tag149 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions149 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values149 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values149 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand150 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 257))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 54)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 243)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 244)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 249)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 252)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 266)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 267)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 270)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 271)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 272))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 274))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 61⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions150 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 396])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 193]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 382]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 383]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 388]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 391]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 405]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 406]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 409]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 410]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 411])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 413])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup150 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions150⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields150 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 396])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 193]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 382]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 383]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 388]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 391]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 405]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 406]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 409]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 410]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 411])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 413])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values150 (logical : Nat → F) :
    (sourceExpressions150.map (Verification.environment logical)).toList = sourceFields150 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag150 (logical : Nat → F) :
    ((sourceFields150 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics150 (logical : Nat → F) :
    (sourceLookup150).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields150 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions150.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values150]
    exact source_tag150 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions150 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values150 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values150 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand151 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 259))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 269))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 275))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 62⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions151 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 398])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 408])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 414])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup151 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions151⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields151 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 398])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 408])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 414])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values151 (logical : Nat → F) :
    (sourceExpressions151.map (Verification.environment logical)).toList = sourceFields151 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag151 (logical : Nat → F) :
    ((sourceFields151 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics151 (logical : Nat → F) :
    (sourceLookup151).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields151 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions151.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values151]
    exact source_tag151 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions151 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values151 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values151 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand152 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 260))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 271))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 276))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 63⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions152 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 399])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 410])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 415])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup152 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions152⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields152 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 399])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 410])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 415])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values152 (logical : Nat → F) :
    (sourceExpressions152.map (Verification.environment logical)).toList = sourceFields152 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag152 (logical : Nat → F) :
    ((sourceFields152 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics152 (logical : Nat → F) :
    (sourceLookup152).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields152 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions152.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values152]
    exact source_tag152 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions152 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values152 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values152 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand153 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 265))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 277))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 278))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 281))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 64⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions153 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 404])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 416])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 417])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 420])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup153 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions153⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields153 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 404])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 416])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 417])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 420])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values153 (logical : Nat → F) :
    (sourceExpressions153.map (Verification.environment logical)).toList = sourceFields153 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag153 (logical : Nat → F) :
    ((sourceFields153 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics153 (logical : Nat → F) :
    (sourceLookup153).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields153 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions153.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values153]
    exact source_tag153 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions153 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values153 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values153 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand154 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 268))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 16)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 32)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 85)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 87)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 101)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 118)), (⟨⟨134217727, by decide⟩⟩, (.BaseLayerWitness 138)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 139)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 142)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 193)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 196)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 277)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 278))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 282))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 65⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions154 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 407])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 155]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 171]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 224]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 226]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 240]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 257]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 277]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 278]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 281]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 332]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 335]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 416]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 417])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 421])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup154 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions154⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields154 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 407])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 155]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 171]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 224]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 226]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 240]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 257]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 277]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 278]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 281]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 332]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 335]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 416]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 417])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 421])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values154 (logical : Nat → F) :
    (sourceExpressions154.map (Verification.environment logical)).toList = sourceFields154 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag154 (logical : Nat → F) :
    ((sourceFields154 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics154 (logical : Nat → F) :
    (sourceLookup154).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields154 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions154.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values154]
    exact source_tag154 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions154 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values154 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values154 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand155 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 266))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 279))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 280))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 283))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 66⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions155 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 405])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 418])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 419])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 422])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup155 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions155⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields155 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 405])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 418])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 419])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 422])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values155 (logical : Nat → F) :
    (sourceExpressions155.map (Verification.environment logical)).toList = sourceFields155 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag155 (logical : Nat → F) :
    ((sourceFields155 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics155 (logical : Nat → F) :
    (sourceLookup155).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields155 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions155.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values155]
    exact source_tag155 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions155 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values155 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values155 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.BlakeRound
