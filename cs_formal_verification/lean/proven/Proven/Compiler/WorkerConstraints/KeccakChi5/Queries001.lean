module
public import Proven.Compiler.WorkerConstraints.Values
public import Proven.Compiler.WorkerConstraints.Setup
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakChi5
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One actual resolved primitive operand. -/
noncomputable def operand12 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 9))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 21))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 33))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 45))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 57))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 69))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 81))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 93))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 105))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 117))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177142, by decide⟩⟩⟩], 11⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions12 : Vector (Airbender.Expression F) 11 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 63])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 75])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 99])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 111])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 123])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 135])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 147])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 159])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 171])]), Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup12 : Lookup F := ⟨(WorkerConstraints.setupTable .chi5).toRaw, sourceExpressions12⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields12 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 63])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 75])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 87])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 99])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 111])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 123])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 135])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 147])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 159])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 171])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values12 (logical : Nat → F) :
    (sourceExpressions12.map (Verification.environment logical)).toList = sourceFields12 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag12 (logical : Nat → F) :
    ((sourceFields12 logical)[10]?).getD 0 ≠ 0 := by
  change (65 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics12 (logical : Nat → F) :
    (sourceLookup12).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields12 logical = NativeWorkerSetup.rows .chi5 0 index := by
  have tag : (((sourceExpressions12.map (Verification.environment logical)).toList)[width .chi5 - 1]?).getD 0 ≠ 0 := by
    rw [source_values12]
    exact source_tag12 logical
  have equivalent := generic_lookup_refinement .chi5 sourceExpressions12 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values12 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values12 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand13 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 15)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 7)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 8)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 9))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 26)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 19)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 21))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 37)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 31)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 32)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 33))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 48)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 43)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 44)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 45))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 59)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 55)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 56)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 57))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 17)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 67)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 68)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 69))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 28)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 79)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 80)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 81))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 39)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 91)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 92)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 93))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 50)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 103)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 104)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 105))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 61)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 115)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 116)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 117))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177142, by decide⟩⟩⟩], 12⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions13 : Vector (Airbender.Expression F) 11 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 18]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 61]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 62]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 63])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 26]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 73]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 74]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 75])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 34]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 87])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 42]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 97]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 98]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 99])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 50]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 109]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 110]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 111])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 20]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 121]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 122]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 123])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 28]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 133]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 134]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 135])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 36]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 145]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 146]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 147])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 44]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 157]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 158]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 159])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 52]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 169]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 170]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 171])]), Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup13 : Lookup F := ⟨(WorkerConstraints.setupTable .chi5).toRaw, sourceExpressions13⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields13 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 18]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 61]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 62]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 63])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 26]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 73]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 74]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 75])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 34]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 85]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 86]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 87])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 42]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 97]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 98]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 99])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 50]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 109]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 110]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 111])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 20]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 121]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 122]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 123])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 28]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 133]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 134]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 135])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 36]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 145]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 146]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 147])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 44]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 157]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 158]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 159])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 52]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 169]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 170]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 171])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values13 (logical : Nat → F) :
    (sourceExpressions13.map (Verification.environment logical)).toList = sourceFields13 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag13 (logical : Nat → F) :
    ((sourceFields13 logical)[10]?).getD 0 ≠ 0 := by
  change (65 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics13 (logical : Nat → F) :
    (sourceLookup13).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields13 logical = NativeWorkerSetup.rows .chi5 0 index := by
  have tag : (((sourceExpressions13.map (Verification.environment logical)).toList)[width .chi5 - 1]?).getD 0 ≠ 0 := by
    rw [source_values13]
    exact source_tag13 logical
  have equivalent := generic_lookup_refinement .chi5 sourceExpressions13 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values13 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values13 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand14 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 10))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 22))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 34))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 46))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 58))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 70))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 82))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 94))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 106))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 118))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177142, by decide⟩⟩⟩], 13⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions14 : Vector (Airbender.Expression F) 11 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 64])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 76])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 88])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 100])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 112])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 124])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 136])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 148])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 160])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 172])]), Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup14 : Lookup F := ⟨(WorkerConstraints.setupTable .chi5).toRaw, sourceExpressions14⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields14 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 64])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 76])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 88])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 100])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 112])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 124])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 136])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 148])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 160])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 172])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values14 (logical : Nat → F) :
    (sourceExpressions14.map (Verification.environment logical)).toList = sourceFields14 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag14 (logical : Nat → F) :
    ((sourceFields14 logical)[10]?).getD 0 ≠ 0 := by
  change (65 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics14 (logical : Nat → F) :
    (sourceLookup14).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields14 logical = NativeWorkerSetup.rows .chi5 0 index := by
  have tag : (((sourceExpressions14.map (Verification.environment logical)).toList)[width .chi5 - 1]?).getD 0 ≠ 0 := by
    rw [source_values14]
    exact source_tag14 logical
  have equivalent := generic_lookup_refinement .chi5 sourceExpressions14 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values14 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values14 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand15 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 11))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 23))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 35))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 47))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 59))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 71))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 83))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 95))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 107))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 119))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177142, by decide⟩⟩⟩], 14⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions15 : Vector (Airbender.Expression F) 11 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 65])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 77])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 89])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 101])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 113])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 125])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 137])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 149])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 161])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 173])]), Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup15 : Lookup F := ⟨(WorkerConstraints.setupTable .chi5).toRaw, sourceExpressions15⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields15 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 65])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 77])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 89])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 101])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 113])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 125])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 137])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 149])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 161])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 173])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values15 (logical : Nat → F) :
    (sourceExpressions15.map (Verification.environment logical)).toList = sourceFields15 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag15 (logical : Nat → F) :
    ((sourceFields15 logical)[10]?).getD 0 ≠ 0 := by
  change (65 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics15 (logical : Nat → F) :
    (sourceLookup15).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields15 logical = NativeWorkerSetup.rows .chi5 0 index := by
  have tag : (((sourceExpressions15.map (Verification.environment logical)).toList)[width .chi5 - 1]?).getD 0 ≠ 0 := by
    rw [source_values15]
    exact source_tag15 logical
  have equivalent := generic_lookup_refinement .chi5 sourceExpressions15 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values15 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values15 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand16 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 12))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 36))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 48))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 60))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 72))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 84))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 96))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 108))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 120))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177142, by decide⟩⟩⟩], 15⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions16 : Vector (Airbender.Expression F) 11 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 66])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 78])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 90])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 102])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 114])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 126])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 138])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 150])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 162])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 174])]), Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup16 : Lookup F := ⟨(WorkerConstraints.setupTable .chi5).toRaw, sourceExpressions16⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields16 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 66])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 78])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 90])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 102])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 114])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 126])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 138])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 150])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 162])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 174])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values16 (logical : Nat → F) :
    (sourceExpressions16.map (Verification.environment logical)).toList = sourceFields16 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag16 (logical : Nat → F) :
    ((sourceFields16 logical)[10]?).getD 0 ≠ 0 := by
  change (65 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics16 (logical : Nat → F) :
    (sourceLookup16).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields16 logical = NativeWorkerSetup.rows .chi5 0 index := by
  have tag : (((sourceExpressions16.map (Verification.environment logical)).toList)[width .chi5 - 1]?).getD 0 ≠ 0 := by
    rw [source_values16]
    exact source_tag16 logical
  have equivalent := generic_lookup_refinement .chi5 sourceExpressions16 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values16 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values16 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand17 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 16)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 10)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 11)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 12))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 27)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 23)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 24))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 38)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 34)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 35)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 36))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 49)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 46)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 47)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 48))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 60)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 58)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 59)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 60))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 18)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 70)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 71)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 72))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 29)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 82)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 83)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 84))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 40)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 94)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 95)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 96))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 51)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 106)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 107)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 108))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerMemory 62)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 118)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 119)), (⟨⟨1744830465, by decide⟩⟩, (.BaseLayerWitness 120))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177142, by decide⟩⟩⟩], 16⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions17 : Vector (Airbender.Expression F) 11 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 19]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 64]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 65]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 66])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 27]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 76]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 77]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 78])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 35]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 88]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 89]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 90])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 43]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 100]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 101]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 102])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 51]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 112]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 113]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 114])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 21]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 124]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 125]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 126])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 29]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 136]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 137]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 138])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 37]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 148]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 149]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 150])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 45]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 160]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 161]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 162])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 53]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 172]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 173]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 174])]), Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup17 : Lookup F := ⟨(WorkerConstraints.setupTable .chi5).toRaw, sourceExpressions17⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields17 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 19]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 64]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 65]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 66])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 27]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 76]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 77]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 78])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 35]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 88]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 89]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 90])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 43]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 100]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 101]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 102])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 51]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 112]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 113]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 114])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 21]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 124]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 125]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 126])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 29]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 136]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 137]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 138])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 37]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 148]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 149]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 150])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 45]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 160]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 161]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 162])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 53]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 172]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 173]), (.Product #[.Constant ⟨⟨1744830465, by decide⟩⟩, .Var 174])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177142, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values17 (logical : Nat → F) :
    (sourceExpressions17.map (Verification.environment logical)).toList = sourceFields17 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag17 (logical : Nat → F) :
    ((sourceFields17 logical)[10]?).getD 0 ≠ 0 := by
  change (65 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics17 (logical : Nat → F) :
    (sourceLookup17).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields17 logical = NativeWorkerSetup.rows .chi5 0 index := by
  have tag : (((sourceExpressions17.map (Verification.environment logical)).toList)[width .chi5 - 1]?).getD 0 ≠ 0 := by
    rw [source_values17]
    exact source_tag17 logical
  have equivalent := generic_lookup_refinement .chi5 sourceExpressions17 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values17 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values17 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand18 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 6))], ⟨⟨0, by decide⟩⟩⟩, 1⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions18 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 12])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup18 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions18⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields18 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 12])])).eval (Verification.environment logical)]

theorem source_values18 (logical : Nat → F) :
    (sourceExpressions18.map (Verification.environment logical)).toList = sourceFields18 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics18 (logical : Nat → F) :
    (sourceLookup18).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields18 logical = NativeWorkerSetup.rows .chi5 2 index := by
  simpa only [sourceLookup18, sourceExpressions18, sourceFields18, Trace.timestampLookup] using
    timestamp_refinement .chi5 (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 12])])) logical


end Airbender.Compiler.WorkerConstraints.KeccakChi5
