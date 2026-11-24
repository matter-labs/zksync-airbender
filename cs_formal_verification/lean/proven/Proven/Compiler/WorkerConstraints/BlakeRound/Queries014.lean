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
noncomputable def operand168 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 298))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 304))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨2013265920, by decide⟩⟩, (.BaseLayerMemory 116)), (⟨⟨2013200385, by decide⟩⟩, (.BaseLayerMemory 117)), (⟨⟨1, by decide⟩⟩, (.BaseLayerMemory 146)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerMemory 147)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 51)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 52)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 203)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 204)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 205)), (⟨⟨256, by decide⟩⟩, (.BaseLayerWitness 206)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 212)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 225)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 226)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 227)), (⟨⟨256, by decide⟩⟩, (.BaseLayerWitness 228)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 232)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 281)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 282)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 283)), (⟨⟨256, by decide⟩⟩, (.BaseLayerWitness 284)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 290))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨8388608, by decide⟩⟩, (.BaseLayerMemory 86)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 305))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939523977, by decide⟩⟩⟩], 79⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions168 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 437])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 443])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013265920, by decide⟩⟩, .Var 79]), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 80]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 99]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 100]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 190]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 191]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 342]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 343]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 344]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 345]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 351]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 364]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 365]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 366]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 367]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 371]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 420]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 421]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 422]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 423]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 429])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 59]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 444])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939523977, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup168 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions168⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields168 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 437])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 443])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013265920, by decide⟩⟩, .Var 79]), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 80]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 99]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 100]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 190]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 191]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 342]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 343]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 344]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 345]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 351]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 364]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 365]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 366]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 367]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 371]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 420]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 421]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 422]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 423]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 429])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 59]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 444])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939523977, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values168 (logical : Nat → F) :
    (sourceExpressions168.map (Verification.environment logical)).toList = sourceFields168 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag168 (logical : Nat → F) :
    ((sourceFields168 logical)[5]?).getD 0 ≠ 0 := by
  change (56 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics168 (logical : Nat → F) :
    (sourceLookup168).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields168 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions168.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values168]
    exact source_tag168 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions168 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values168 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values168 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand169 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 145))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 307))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 308))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 311))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 80⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions169 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 284])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 446])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 447])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 450])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup169 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions169⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields169 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 284])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 446])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 447])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 450])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values169 (logical : Nat → F) :
    (sourceExpressions169.map (Verification.environment logical)).toList = sourceFields169 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag169 (logical : Nat → F) :
    ((sourceFields169 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics169 (logical : Nat → F) :
    (sourceLookup169).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields169 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions169.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values169]
    exact source_tag169 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions169 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values169 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values169 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand170 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 148))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 36)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 89)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 91)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 105)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 158)), (⟨⟨134217727, by decide⟩⟩, (.BaseLayerWitness 178)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 179)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 182)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 233)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 236)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 307)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 308))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 312))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 81⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions170 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 287])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 159]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 175]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 228]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 230]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 244]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 297]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 317]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 318]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 321]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 372]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 375]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 446]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 447])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 451])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup170 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions170⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields170 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 287])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 159]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 175]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 228]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 230]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 244]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 297]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 317]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 318]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 321]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 372]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 375]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 446]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 447])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 451])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values170 (logical : Nat → F) :
    (sourceExpressions170.map (Verification.environment logical)).toList = sourceFields170 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag170 (logical : Nat → F) :
    ((sourceFields170 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics170 (logical : Nat → F) :
    (sourceLookup170).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields170 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions170.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values170]
    exact source_tag170 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions170 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values170 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values170 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand171 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 146))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 309))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 310))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 313))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 82⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions171 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 285])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 448])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 449])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 452])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup171 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions171⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields171 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 285])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 448])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 449])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 452])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values171 (logical : Nat → F) :
    (sourceExpressions171.map (Verification.environment logical)).toList = sourceFields171 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag171 (logical : Nat → F) :
    ((sourceFields171 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics171 (logical : Nat → F) :
    (sourceLookup171).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields171 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions171.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values171]
    exact source_tag171 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions171 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values171 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values171 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand172 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 147))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 38)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 90)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 92)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 106)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 158)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 160)), (⟨⟨134217727, by decide⟩⟩, (.BaseLayerWitness 177)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 180)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 182)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 184)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 234)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 235)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 308)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 309)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 310))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 314))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 83⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions172 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 286])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 161]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 177]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 229]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 231]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 245]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 297]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 299]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 316]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 319]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 321]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 323]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 373]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 374]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 447]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 448]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 449])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 453])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup172 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions172⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields172 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 286])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 161]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 177]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 229]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 231]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 245]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 297]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 299]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 316]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 319]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 321]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 323]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 373]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 374]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 447]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 448]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 449])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 453])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values172 (logical : Nat → F) :
    (sourceExpressions172.map (Verification.environment logical)).toList = sourceFields172 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag172 (logical : Nat → F) :
    ((sourceFields172 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics172 (logical : Nat → F) :
    (sourceLookup172).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields172 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions172.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values172]
    exact source_tag172 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions172 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values172 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values172 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand173 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 322))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 316))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 325))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 84⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions173 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 461])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 455])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 464])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup173 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions173⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields173 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 461])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 455])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 464])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values173 (logical : Nat → F) :
    (sourceExpressions173.map (Verification.environment logical)).toList = sourceFields173 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag173 (logical : Nat → F) :
    ((sourceFields173 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics173 (logical : Nat → F) :
    (sourceLookup173).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields173 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions173.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values173]
    exact source_tag173 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions173 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values173 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values173 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand174 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 324))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 319))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 326))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 85⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions174 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 463])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 458])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 465])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup174 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions174⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields174 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 463])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 458])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 465])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values174 (logical : Nat → F) :
    (sourceExpressions174.map (Verification.environment logical)).toList = sourceFields174 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag174 (logical : Nat → F) :
    ((sourceFields174 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics174 (logical : Nat → F) :
    (sourceLookup174).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields174 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions174.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values174]
    exact source_tag174 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions174 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values174 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values174 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand175 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 233)), (⟨⟨536870912, by decide⟩⟩, (.BaseLayerWitness 236)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 321)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 322))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 323))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 53)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 245)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 246)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 249)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 265)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 268)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 270)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 313)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 314)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 315)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 316)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 317))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 318))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 327))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1207959431, by decide⟩⟩⟩], 86⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions175 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 372]), (.Product #[.Constant ⟨⟨536870912, by decide⟩⟩, .Var 375]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 460]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 461])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 462])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 192]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 384]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 385]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 388]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 404]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 407]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 409]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 452]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 453]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 454]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 455]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 456])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 457])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 466])]), Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup175 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions175⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields175 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 372]), (.Product #[.Constant ⟨⟨536870912, by decide⟩⟩, .Var 375]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 460]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 461])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 462])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 192]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 384]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 385]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 388]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 404]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 407]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 409]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 452]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 453]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 454]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 455]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 456])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 457])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 466])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values175 (logical : Nat → F) :
    (sourceExpressions175.map (Verification.environment logical)).toList = sourceFields175 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag175 (logical : Nat → F) :
    ((sourceFields175 logical)[5]?).getD 0 ≠ 0 := by
  change (57 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics175 (logical : Nat → F) :
    (sourceLookup175).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields175 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions175.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values175]
    exact source_tag175 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions175 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values175 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values175 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand176 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 234)), (⟨⟨536870912, by decide⟩⟩, (.BaseLayerWitness 235)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 323)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 324))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 321))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 54)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 243)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 244)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 249)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 252)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 266)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 267)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 270)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 272)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 311)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 312)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 317)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 318)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 319)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 320))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 315))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 328))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1207959431, by decide⟩⟩⟩], 87⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions176 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 373]), (.Product #[.Constant ⟨⟨536870912, by decide⟩⟩, .Var 374]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 462]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 463])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 460])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 193]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 382]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 383]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 388]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 391]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 405]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 406]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 409]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 411]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 450]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 451]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 456]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 457]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 458]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 459])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 454])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 467])]), Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup176 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions176⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields176 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 373]), (.Product #[.Constant ⟨⟨536870912, by decide⟩⟩, .Var 374]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 462]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 463])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 460])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 193]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 382]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 383]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 388]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 391]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 405]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 406]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 409]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 411]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 450]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 451]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 456]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 457]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 458]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 459])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 454])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 467])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values176 (logical : Nat → F) :
    (sourceExpressions176.map (Verification.environment logical)).toList = sourceFields176 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag176 (logical : Nat → F) :
    ((sourceFields176 logical)[5]?).getD 0 ≠ 0 := by
  change (57 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics176 (logical : Nat → F) :
    (sourceLookup176).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields176 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions176.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values176]
    exact source_tag176 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions176 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values176 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values176 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand177 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 314))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 62)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 329))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 331))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 88⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions177 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 453])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 43]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 468])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 470])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup177 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions177⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields177 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 453])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 43]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 468])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 470])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values177 (logical : Nat → F) :
    (sourceExpressions177.map (Verification.environment logical)).toList = sourceFields177 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag177 (logical : Nat → F) :
    ((sourceFields177 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics177 (logical : Nat → F) :
    (sourceLookup177).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields177 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions177.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values177]
    exact source_tag177 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions177 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values177 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values177 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand178 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 312))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 63)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 330))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 332))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 89⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions178 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 451])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 44]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 469])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 471])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup178 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions178⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields178 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 451])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 44]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 469])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 471])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values178 (logical : Nat → F) :
    (sourceExpressions178.map (Verification.environment logical)).toList = sourceFields178 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag178 (logical : Nat → F) :
    ((sourceFields178 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics178 (logical : Nat → F) :
    (sourceLookup178).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields178 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions178.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values178]
    exact source_tag178 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions178 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values178 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values178 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand179 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 313))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 329))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerMemory 62)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 36)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 89)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 91)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 105)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 107)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 158)), (⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 178)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 179)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 182)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 233)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 236)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 308)), (⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 326)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 327))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 129)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 332))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 90⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions179 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 452])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 468])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 43]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 159]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 175]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 228]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 230]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 244]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 246]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 297]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 317]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 318]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 321]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 372]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 375]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 447]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 465]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 466])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 88]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 471])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup179 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions179⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields179 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 452])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 468])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 43]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 159]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 175]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 228]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 230]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 244]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 246]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 297]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 317]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 318]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 321]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 372]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 375]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 447]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 465]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 466])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 88]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 471])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values179 (logical : Nat → F) :
    (sourceExpressions179.map (Verification.environment logical)).toList = sourceFields179 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag179 (logical : Nat → F) :
    ((sourceFields179 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics179 (logical : Nat → F) :
    (sourceLookup179).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields179 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions179.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values179]
    exact source_tag179 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions179 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values179 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values179 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.BlakeRound
