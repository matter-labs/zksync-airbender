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
noncomputable def operand84 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 213)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 534))], ⟨⟨133099247, by decide⟩⟩⟩, 84⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions84 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 756]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 757])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup84 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions84⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields84 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 756]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 757])])).eval (Verification.environment logical)]

theorem source_values84 (logical : Nat → F) :
    (sourceExpressions84.map (Verification.environment logical)).toList = sourceFields84 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics84 (logical : Nat → F) :
    (sourceLookup84).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields84 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup84, sourceExpressions84, sourceFields84, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 756]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 757])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand85 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 216)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 535))], ⟨⟨1476395013, by decide⟩⟩⟩, 85⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions85 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 758]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 760])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup85 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions85⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields85 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 758]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 760])])).eval (Verification.environment logical)]

theorem source_values85 (logical : Nat → F) :
    (sourceExpressions85.map (Verification.environment logical)).toList = sourceFields85 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics85 (logical : Nat → F) :
    (sourceLookup85).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields85 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup85, sourceExpressions85, sourceFields85, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 758]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 760])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand86 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 217)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 535))], ⟨⟨133099247, by decide⟩⟩⟩, 86⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions86 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 759]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 760])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup86 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions86⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields86 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 759]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 760])])).eval (Verification.environment logical)]

theorem source_values86 (logical : Nat → F) :
    (sourceExpressions86.map (Verification.environment logical)).toList = sourceFields86 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics86 (logical : Nat → F) :
    (sourceLookup86).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields86 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup86, sourceExpressions86, sourceFields86, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 759]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 760])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand87 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 2))], ⟨⟨0, by decide⟩⟩⟩, 87⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions87 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 3])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup87 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions87⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields87 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 3])])).eval (Verification.environment logical)]

theorem source_values87 (logical : Nat → F) :
    (sourceExpressions87.map (Verification.environment logical)).toList = sourceFields87 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics87 (logical : Nat → F) :
    (sourceLookup87).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields87 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup87, sourceExpressions87, sourceFields87, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 3])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand88 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨67108864, by decide⟩⟩, (.BaseLayerMemory 150))], ⟨⟨0, by decide⟩⟩⟩, 88⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions88 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨67108864, by decide⟩⟩, .Var 101])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup88 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions88⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields88 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨67108864, by decide⟩⟩, .Var 101])])).eval (Verification.environment logical)]

theorem source_values88 (logical : Nat → F) :
    (sourceExpressions88.map (Verification.environment logical)).toList = sourceFields88 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics88 (logical : Nat → F) :
    (sourceLookup88).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields88 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup88, sourceExpressions88, sourceFields88, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨67108864, by decide⟩⟩, .Var 101])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand89 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 121))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 117))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 118))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 123))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 0⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions89 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 260])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 256])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 257])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 262])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup89 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions89⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields89 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 260])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 256])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 257])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 262])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values89 (logical : Nat → F) :
    (sourceExpressions89.map (Verification.environment logical)).toList = sourceFields89 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag89 (logical : Nat → F) :
    ((sourceFields89 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics89 (logical : Nat → F) :
    (sourceLookup89).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields89 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions89.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values89]
    exact source_tag89 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions89 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values89 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values89 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand90 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 59)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 121))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 16)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 32)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 85)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 117)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 118))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 124))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 1⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions90 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 198]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 260])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 155]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 171]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 224]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 256]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 257])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 263])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup90 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions90⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields90 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 198]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 260])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 155]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 171]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 224]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 256]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 257])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 263])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values90 (logical : Nat → F) :
    (sourceExpressions90.map (Verification.environment logical)).toList = sourceFields90 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag90 (logical : Nat → F) :
    ((sourceFields90 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics90 (logical : Nat → F) :
    (sourceLookup90).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields90 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions90.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values90]
    exact source_tag90 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions90 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values90 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values90 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand91 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 122))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 119))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 120))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 125))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 2⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions91 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 261])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 258])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 259])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 264])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup91 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions91⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields91 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 261])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 258])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 259])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 264])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values91 (logical : Nat → F) :
    (sourceExpressions91.map (Verification.environment logical)).toList = sourceFields91 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag91 (logical : Nat → F) :
    ((sourceFields91 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics91 (logical : Nat → F) :
    (sourceLookup91).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields91 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions91.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values91]
    exact source_tag91 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions91 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values91 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values91 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand92 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 60)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 122))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 18)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 34)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 86)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 118)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 119)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 120))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 126))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 3⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions92 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 199]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 261])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 157]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 173]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 225]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 257]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 258]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 259])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 265])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup92 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions92⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields92 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 199]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 261])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 157]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 173]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 225]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 257]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 258]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 259])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 265])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values92 (logical : Nat → F) :
    (sourceExpressions92.map (Verification.environment logical)).toList = sourceFields92 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag92 (logical : Nat → F) :
    ((sourceFields92 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics92 (logical : Nat → F) :
    (sourceLookup92).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields92 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions92.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values92]
    exact source_tag92 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions92 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values92 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values92 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand93 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 134))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 128))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 137))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 4⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions93 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 273])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 267])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 276])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup93 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions93⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields93 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 273])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 267])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 276])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values93 (logical : Nat → F) :
    (sourceExpressions93.map (Verification.environment logical)).toList = sourceFields93 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag93 (logical : Nat → F) :
    ((sourceFields93 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics93 (logical : Nat → F) :
    (sourceLookup93).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields93 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions93.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values93]
    exact source_tag93 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions93 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values93 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values93 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand94 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 136))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 131))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 138))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 5⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions94 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 275])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 270])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 277])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup94 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions94⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields94 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 275])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 270])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 277])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values94 (logical : Nat → F) :
    (sourceExpressions94.map (Verification.environment logical)).toList = sourceFields94 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag94 (logical : Nat → F) :
    ((sourceFields94 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics94 (logical : Nat → F) :
    (sourceLookup94).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields94 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions94.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values94]
    exact source_tag94 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions94 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values94 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values94 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand95 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 32)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 133)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 134))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 135))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 47)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 125)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 126)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 127)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 128)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 129))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 130))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 139))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1207959431, by decide⟩⟩⟩], 6⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions95 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 171]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 272]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 273])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 274])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 186]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 264]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 265]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 266]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 267]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 268])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 269])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 278])]), Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup95 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions95⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields95 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 171]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 272]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 273])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 274])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 186]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 264]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 265]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 266]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 267]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 268])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 269])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 278])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values95 (logical : Nat → F) :
    (sourceExpressions95.map (Verification.environment logical)).toList = sourceFields95 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag95 (logical : Nat → F) :
    ((sourceFields95 logical)[5]?).getD 0 ≠ 0 := by
  change (57 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics95 (logical : Nat → F) :
    (sourceLookup95).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields95 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions95.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values95]
    exact source_tag95 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions95 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values95 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values95 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.BlakeRound
