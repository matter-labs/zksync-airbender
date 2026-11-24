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
noncomputable def operand108 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 56)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 162))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 38)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 90)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 158)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 159)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 160))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 166))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 19⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions108 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 195]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 301])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 161]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 177]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 229]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 297]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 298]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 299])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 305])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup108 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions108⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields108 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 195]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 301])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 161]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 177]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 229]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 297]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 298]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 299])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 305])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values108 (logical : Nat → F) :
    (sourceExpressions108.map (Verification.environment logical)).toList = sourceFields108 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag108 (logical : Nat → F) :
    ((sourceFields108 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics108 (logical : Nat → F) :
    (sourceLookup108).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields108 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions108.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values108]
    exact source_tag108 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions108 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values108 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values108 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand109 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 174))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 168))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 177))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 20⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions109 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 313])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 307])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 316])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup109 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions109⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields109 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 313])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 307])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 316])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values109 (logical : Nat → F) :
    (sourceExpressions109.map (Verification.environment logical)).toList = sourceFields109 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag109 (logical : Nat → F) :
    ((sourceFields109 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics109 (logical : Nat → F) :
    (sourceLookup109).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields109 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions109.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values109]
    exact source_tag109 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions109 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values109 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values109 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand110 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 176))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 171))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 178))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 21⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions110 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 315])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 310])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 317])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup110 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions110⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields110 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 315])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 310])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 317])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values110 (logical : Nat → F) :
    (sourceExpressions110.map (Verification.environment logical)).toList = sourceFields110 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag110 (logical : Nat → F) :
    ((sourceFields110 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics110 (logical : Nat → F) :
    (sourceLookup110).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields110 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions110.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values110]
    exact source_tag110 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions110 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values110 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values110 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand111 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 36)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 173)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 174))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 175))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 49)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 165)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 166)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 167)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 168)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 169))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 170))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 179))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1207959431, by decide⟩⟩⟩], 22⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions111 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 175]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 312]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 313])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 314])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 188]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 304]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 305]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 306]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 307]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 308])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 309])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 318])]), Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup111 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions111⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields111 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 175]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 312]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 313])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 314])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 188]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 304]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 305]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 306]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 307]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 308])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 309])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 318])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values111 (logical : Nat → F) :
    (sourceExpressions111.map (Verification.environment logical)).toList = sourceFields111 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag111 (logical : Nat → F) :
    ((sourceFields111 logical)[5]?).getD 0 ≠ 0 := by
  change (57 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics111 (logical : Nat → F) :
    (sourceLookup111).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields111 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions111.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values111]
    exact source_tag111 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions111 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values111 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values111 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand112 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 38)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 175)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 176))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 173))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 50)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 163)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 164)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 169)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 170)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 171)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 172))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 167))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 180))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1207959431, by decide⟩⟩⟩], 23⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions112 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 177]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 314]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 315])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 312])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 189]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 302]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 303]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 308]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 309]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 310]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 311])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 306])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 319])]), Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup112 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions112⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields112 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 177]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 314]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 315])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 312])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 189]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 302]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 303]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 308]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 309]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 310]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 311])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 306])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 319])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values112 (logical : Nat → F) :
    (sourceExpressions112.map (Verification.environment logical)).toList = sourceFields112 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag112 (logical : Nat → F) :
    ((sourceFields112 logical)[5]?).getD 0 ≠ 0 := by
  change (57 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics112 (logical : Nat → F) :
    (sourceLookup112).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields112 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions112.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values112]
    exact source_tag112 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions112 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values112 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values112 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand113 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 166))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 36)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 89)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 91)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 158)), (⟨⟨134217727, by decide⟩⟩, (.BaseLayerWitness 178)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 179)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 181)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 182))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 185))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 24⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions113 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 305])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 159]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 175]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 228]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 230]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 297]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 317]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 318]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 320]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 321])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 324])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup113 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions113⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields113 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 305])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 159]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 175]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 228]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 230]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 297]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 317]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 318]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 320]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 321])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 324])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values113 (logical : Nat → F) :
    (sourceExpressions113.map (Verification.environment logical)).toList = sourceFields113 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag113 (logical : Nat → F) :
    ((sourceFields113 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics113 (logical : Nat → F) :
    (sourceLookup113).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields113 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions113.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values113]
    exact source_tag113 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions113 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values113 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values113 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand114 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 164))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 38)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 90)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 92)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 158)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 160)), (⟨⟨134217727, by decide⟩⟩, (.BaseLayerWitness 177)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 180)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 182)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 183)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 184))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 186))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 25⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions114 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 303])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 161]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 177]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 229]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 231]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 297]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 299]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 316]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 319]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 321]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 322]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 323])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 325])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup114 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions114⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields114 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 303])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 161]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 177]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 229]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 231]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 297]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 299]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 316]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 319]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 321]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 322]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 323])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 325])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values114 (logical : Nat → F) :
    (sourceExpressions114.map (Verification.environment logical)).toList = sourceFields114 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag114 (logical : Nat → F) :
    ((sourceFields114 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics114 (logical : Nat → F) :
    (sourceLookup114).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields114 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions114.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values114]
    exact source_tag114 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions114 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values114 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values114 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand115 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 165))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 181))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 182))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 187))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 26⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions115 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 304])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 320])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 321])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 326])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup115 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions115⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields115 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 304])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 320])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 321])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 326])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values115 (logical : Nat → F) :
    (sourceExpressions115.map (Verification.environment logical)).toList = sourceFields115 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag115 (logical : Nat → F) :
    ((sourceFields115 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics115 (logical : Nat → F) :
    (sourceLookup115).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields115 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions115.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values115]
    exact source_tag115 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions115 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values115 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values115 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand116 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 163))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 183))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 184))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 188))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 27⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions116 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 302])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 322])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 323])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 327])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup116 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions116⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields116 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 302])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 322])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 323])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 327])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values116 (logical : Nat → F) :
    (sourceExpressions116.map (Verification.environment logical)).toList = sourceFields116 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag116 (logical : Nat → F) :
    ((sourceFields116 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics116 (logical : Nat → F) :
    (sourceLookup116).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields116 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions116.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values116]
    exact source_tag116 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions116 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values116 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values116 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand117 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 178))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 49)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 165)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 166)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 169)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 185)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 188)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 189)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 190))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 193))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 28⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions117 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 317])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 188]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 304]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 305]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 308]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 324]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 327]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 328]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 329])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 332])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup117 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions117⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields117 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 317])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 188]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 304]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 305]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 308]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 324]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 327]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 328]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 329])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 332])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values117 (logical : Nat → F) :
    (sourceExpressions117.map (Verification.environment logical)).toList = sourceFields117 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag117 (logical : Nat → F) :
    ((sourceFields117 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics117 (logical : Nat → F) :
    (sourceLookup117).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields117 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions117.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values117]
    exact source_tag117 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions117 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values117 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values117 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand118 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 177))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 50)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 163)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 164)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 169)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 172)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 186)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 187)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 190)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 191)), (⟨⟨1476396101, by decide⟩⟩, (.BaseLayerWitness 192))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 194))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 29⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions118 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 316])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 189]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 302]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 303]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 308]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 311]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 325]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 326]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 329]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 330]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 331])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 333])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup118 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions118⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields118 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 316])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 189]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 302]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 303]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 308]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 311]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 325]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 326]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 329]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 330]), (.Product #[.Constant ⟨⟨1476396101, by decide⟩⟩, .Var 331])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 333])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values118 (logical : Nat → F) :
    (sourceExpressions118.map (Verification.environment logical)).toList = sourceFields118 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag118 (logical : Nat → F) :
    ((sourceFields118 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics118 (logical : Nat → F) :
    (sourceLookup118).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields118 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions118.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values118]
    exact source_tag118 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions118 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values118 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values118 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand119 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 179))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 189))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 195))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741784, by decide⟩⟩⟩], 30⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions119 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 318])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 328])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 334])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup119 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions119⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields119 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 318])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 328])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 334])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741784, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values119 (logical : Nat → F) :
    (sourceExpressions119.map (Verification.environment logical)).toList = sourceFields119 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag119 (logical : Nat → F) :
    ((sourceFields119 logical)[5]?).getD 0 ≠ 0 := by
  change (19 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics119 (logical : Nat → F) :
    (sourceLookup119).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields119 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions119.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values119]
    exact source_tag119 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions119 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values119 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values119 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.BlakeRound
