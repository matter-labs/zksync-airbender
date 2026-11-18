module
public import Proven.Compiler.WorkerConstraints.Values
public import Proven.Compiler.WorkerConstraints.Setup
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One actual resolved primitive operand. -/
noncomputable def operand48 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 14))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 26))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 38))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 50))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 62))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 74))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741688, by decide⟩⟩⟩], 19⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions48 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 61])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 73])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 97])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 109])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 121])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup48 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions48⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields48 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 61])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 73])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 85])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 97])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 109])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 121])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values48 (logical : Nat → F) :
    (sourceExpressions48.map (Verification.environment logical)).toList = sourceFields48 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag48 (logical : Nat → F) :
    ((sourceFields48 logical)[7]?).getD 0 ≠ 0 := by
  change (64 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics48 (logical : Nat → F) :
    (sourceLookup48).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields48 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions48.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values48]
    exact source_tag48 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions48 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values48 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values48 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand49 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 15))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 27))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 39))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 51))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 63))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 75))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741688, by decide⟩⟩⟩], 20⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions49 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 62])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 74])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 86])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 98])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 110])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 122])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup49 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions49⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields49 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 62])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 74])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 86])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 98])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 110])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 122])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values49 (logical : Nat → F) :
    (sourceExpressions49.map (Verification.environment logical)).toList = sourceFields49 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag49 (logical : Nat → F) :
    ((sourceFields49 logical)[7]?).getD 0 ≠ 0 := by
  change (64 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics49 (logical : Nat → F) :
    (sourceLookup49).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields49 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions49.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values49]
    exact source_tag49 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions49 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values49 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values49 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand50 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 8))], ⟨⟨0, by decide⟩⟩⟩, 29⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions50 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 13])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup50 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions50⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields50 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 13])])).eval (Verification.environment logical)]

theorem source_values50 (logical : Nat → F) :
    (sourceExpressions50.map (Verification.environment logical)).toList = sourceFields50 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics50 (logical : Nat → F) :
    (sourceLookup50).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields50 logical = NativeWorkerSetup.rows .columnParity 2 index := by
  simpa only [sourceLookup50, sourceExpressions50, sourceFields50, Trace.timestampLookup] using
    timestamp_refinement .columnParity (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 13])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand51 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 22)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 13)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 14)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 15))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 31)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 25)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 26)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 27))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 40)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 37)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 38)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 39))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 49)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 49)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 50)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 51))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 58)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 61)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 62)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 63))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 71)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 73)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 74)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 75))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741688, by decide⟩⟩⟩], 21⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions51 : Vector (Airbender.Expression F) 8 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 22]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 60]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 61]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 62])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 26]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 72]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 73]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 74])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 30]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 86])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 34]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 96]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 97]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 98])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 38]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 108]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 109]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 110])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 46]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 120]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 121]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 122])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup51 : Lookup F := ⟨(WorkerConstraints.setupTable .columnParity).toRaw, sourceExpressions51⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields51 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 22]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 60]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 61]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 62])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 26]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 72]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 73]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 74])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 30]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 86])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 34]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 96]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 97]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 98])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 38]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 108]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 109]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 110])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 46]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 120]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 121]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 122])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741688, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values51 (logical : Nat → F) :
    (sourceExpressions51.map (Verification.environment logical)).toList = sourceFields51 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag51 (logical : Nat → F) :
    ((sourceFields51 logical)[7]?).getD 0 ≠ 0 := by
  change (64 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics51 (logical : Nat → F) :
    (sourceLookup51).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields51 logical = NativeWorkerSetup.rows .columnParity 0 index := by
  have tag : (((sourceExpressions51.map (Verification.environment logical)).toList)[width .columnParity - 1]?).getD 0 ≠ 0 := by
    rw [source_values51]
    exact source_tag51 logical
  have equivalent := generic_lookup_refinement .columnParity sourceExpressions51 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values51 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values51 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
