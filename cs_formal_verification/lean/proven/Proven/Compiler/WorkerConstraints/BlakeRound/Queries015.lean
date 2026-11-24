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
noncomputable def operand180 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 311))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 330))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨2013265920, by decide⟩⟩, (.BaseLayerMemory 62)), (⟨⟨2013200385, by decide⟩⟩, (.BaseLayerMemory 63)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 20)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 22)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 36)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 38)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 89)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 90)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 91)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 92)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 105)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 106)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 107)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 108)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 160)), (⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 177)), (⟨⟨128, by decide⟩⟩, (.BaseLayerWitness 178)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 179)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 180)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 184)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 233)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 234)), (⟨⟨33554432, by decide⟩⟩, (.BaseLayerWitness 235)), (⟨⟨512, by decide⟩⟩, (.BaseLayerWitness 236)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 310)), (⟨⟨8388608, by decide⟩⟩, (.BaseLayerWitness 325)), (⟨⟨128, by decide⟩⟩, (.BaseLayerWitness 326)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 327)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 328))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerMemory 128)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 331))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 91⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions180 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 450])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 469])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013265920, by decide⟩⟩, .Var 43]), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 44]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 159]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 161]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 175]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 177]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 228]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 229]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 230]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 231]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 244]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 245]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 246]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 247]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 299]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 316]), (.Product #[.Constant ⟨⟨128, by decide⟩⟩, .Var 317]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 318]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 319]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 323]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 372]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 373]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 374]), (.Product #[.Constant ⟨⟨512, by decide⟩⟩, .Var 375]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 449]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 464]), (.Product #[.Constant ⟨⟨128, by decide⟩⟩, .Var 465]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 466]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 467])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 470])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup180 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions180⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields180 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 450])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 469])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013265920, by decide⟩⟩, .Var 43]), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 44]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 159]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 161]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 175]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 177]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 228]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 229]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 230]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 231]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 244]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 245]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 246]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 247]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 299]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 316]), (.Product #[.Constant ⟨⟨128, by decide⟩⟩, .Var 317]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 318]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 319]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 323]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 372]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 373]), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 374]), (.Product #[.Constant ⟨⟨512, by decide⟩⟩, .Var 375]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 449]), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 464]), (.Product #[.Constant ⟨⟨128, by decide⟩⟩, .Var 465]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 466]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 467])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 470])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values180 (logical : Nat → F) :
    (sourceExpressions180.map (Verification.environment logical)).toList = sourceFields180 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag180 (logical : Nat → F) :
    ((sourceFields180 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics180 (logical : Nat → F) :
    (sourceLookup180).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields180 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions180.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values180]
    exact source_tag180 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions180 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values180 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values180 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand181 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 326))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 122)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 333))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 335))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 92⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions181 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 465])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 83]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 472])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 474])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup181 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions181⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields181 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 465])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 83]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 472])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 474])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values181 (logical : Nat → F) :
    (sourceExpressions181.map (Verification.environment logical)).toList = sourceFields181 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag181 (logical : Nat → F) :
    ((sourceFields181 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics181 (logical : Nat → F) :
    (sourceLookup181).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields181 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions181.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values181]
    exact source_tag181 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions181 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values181 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values181 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand182 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 325))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨33554432, by decide⟩⟩, (.BaseLayerMemory 123)), (⟨⟨1979711489, by decide⟩⟩, (.BaseLayerWitness 334))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 336))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 93⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions182 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 464])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 473])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 475])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup182 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions182⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields182 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 464])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨33554432, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1979711489, by decide⟩⟩, .Var 473])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 475])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values182 (logical : Nat → F) :
    (sourceExpressions182.map (Verification.environment logical)).toList = sourceFields182 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag182 (logical : Nat → F) :
    ((sourceFields182 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics182 (logical : Nat → F) :
    (sourceLookup182).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields182 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions182.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values182]
    exact source_tag182 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions182 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values182 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values182 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand183 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 327))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 333))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨2013200385, by decide⟩⟩, (.BaseLayerMemory 122)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerMemory 128)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 53)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 245)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 246)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 249)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 265)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 268)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 270)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 313)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 314)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 317))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨8388608, by decide⟩⟩, (.BaseLayerMemory 93)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 336))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939523977, by decide⟩⟩⟩], 94⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions183 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 466])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 472])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 83]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 192]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 384]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 385]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 388]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 404]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 407]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 409]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 452]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 453]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 456])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 64]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 475])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939523977, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup183 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions183⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields183 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 466])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 472])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 83]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 192]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 384]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 385]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 388]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 404]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 407]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 409]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 452]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 453]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 456])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 64]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 475])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939523977, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values183 (logical : Nat → F) :
    (sourceExpressions183.map (Verification.environment logical)).toList = sourceFields183 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag183 (logical : Nat → F) :
    ((sourceFields183 logical)[5]?).getD 0 ≠ 0 := by
  change (56 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics183 (logical : Nat → F) :
    (sourceLookup183).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields183 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions183.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values183]
    exact source_tag183 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions183 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values183 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values183 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand184 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 328))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 334))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨2013265920, by decide⟩⟩, (.BaseLayerMemory 122)), (⟨⟨2013200385, by decide⟩⟩, (.BaseLayerMemory 123)), (⟨⟨1, by decide⟩⟩, (.BaseLayerMemory 128)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerMemory 129)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 53)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 54)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 243)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 244)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 245)), (⟨⟨256, by decide⟩⟩, (.BaseLayerWitness 246)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 252)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 265)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 266)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 267)), (⟨⟨256, by decide⟩⟩, (.BaseLayerWitness 268)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 272)), (⟨⟨65536, by decide⟩⟩, (.BaseLayerWitness 311)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 312)), (⟨⟨1, by decide⟩⟩, (.BaseLayerWitness 313)), (⟨⟨256, by decide⟩⟩, (.BaseLayerWitness 314)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 320))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨8388608, by decide⟩⟩, (.BaseLayerMemory 92)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 335))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨939523977, by decide⟩⟩⟩], 95⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions184 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 467])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 473])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013265920, by decide⟩⟩, .Var 83]), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 88]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 192]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 193]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 382]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 383]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 384]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 385]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 391]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 404]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 405]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 406]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 407]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 411]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 450]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 451]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 452]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 453]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 459])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 63]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 474])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨939523977, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup184 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions184⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields184 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 467])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 473])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨2013265920, by decide⟩⟩, .Var 83]), (.Product #[.Constant ⟨⟨2013200385, by decide⟩⟩, .Var 84]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 87]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 88]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 192]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 193]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 382]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 383]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 384]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 385]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 391]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 404]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 405]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 406]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 407]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 411]), (.Product #[.Constant ⟨⟨65536, by decide⟩⟩, .Var 450]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 451]), (.Product #[.Constant ⟨⟨1, by decide⟩⟩, .Var 452]), (.Product #[.Constant ⟨⟨256, by decide⟩⟩, .Var 453]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 459])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨8388608, by decide⟩⟩, .Var 63]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 474])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨939523977, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values184 (logical : Nat → F) :
    (sourceExpressions184.map (Verification.environment logical)).toList = sourceFields184 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag184 (logical : Nat → F) :
    ((sourceFields184 logical)[5]?).getD 0 ≠ 0 := by
  change (56 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics184 (logical : Nat → F) :
    (sourceLookup184).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields184 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions184.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values184]
    exact source_tag184 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions184 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values184 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values184 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand185 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 185))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 337))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 338))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 341))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 96⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions185 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 324])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 476])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 477])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 480])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup185 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions185⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields185 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 324])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 476])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 477])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 480])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values185 (logical : Nat → F) :
    (sourceExpressions185.map (Verification.environment logical)).toList = sourceFields185 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag185 (logical : Nat → F) :
    ((sourceFields185 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics185 (logical : Nat → F) :
    (sourceLookup185).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields185 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions185.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values185]
    exact source_tag185 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions185 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values185 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values185 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand186 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 188))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 24)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 40)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 93)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 95)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 109)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 198)), (⟨⟨134217727, by decide⟩⟩, (.BaseLayerWitness 218)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 219)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 222)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 273)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 276)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 337)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 338))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 342))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 97⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions186 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 327])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 163]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 179]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 232]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 234]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 248]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 337]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 357]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 358]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 361]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 412]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 415]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 476]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 477])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 481])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup186 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions186⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields186 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 327])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 163]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 179]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 232]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 234]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 248]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 337]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 357]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 358]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 361]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 412]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 415]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 476]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 477])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 481])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values186 (logical : Nat → F) :
    (sourceExpressions186.map (Verification.environment logical)).toList = sourceFields186 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag186 (logical : Nat → F) :
    ((sourceFields186 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics186 (logical : Nat → F) :
    (sourceLookup186).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields186 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions186.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values186]
    exact source_tag186 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions186 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values186 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values186 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand187 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 186))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 339))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 340))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 343))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨671088523, by decide⟩⟩⟩], 98⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions187 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 325])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 478])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 479])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 482])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup187 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions187⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields187 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 325])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 478])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 479])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 482])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨671088523, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values187 (logical : Nat → F) :
    (sourceExpressions187.map (Verification.environment logical)).toList = sourceFields187 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag187 (logical : Nat → F) :
    ((sourceFields187 logical)[5]?).getD 0 ≠ 0 := by
  change (55 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics187 (logical : Nat → F) :
    (sourceLookup187).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields187 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions187.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values187]
    exact source_tag187 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions187 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values187 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values187 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand188 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 187))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 26)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 42)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 94)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 96)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 110)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 198)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 200)), (⟨⟨134217727, by decide⟩⟩, (.BaseLayerWitness 217)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 220)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 222)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 224)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 274)), (⟨⟨536870908, by decide⟩⟩, (.BaseLayerWitness 275)), (⟨⟨16777216, by decide⟩⟩, (.BaseLayerWitness 338)), (⟨⟨1996488705, by decide⟩⟩, (.BaseLayerWitness 339)), (⟨⟨1744831011, by decide⟩⟩, (.BaseLayerWitness 340))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 344))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1073741816, by decide⟩⟩⟩], 99⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions188 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 326])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 165]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 181]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 233]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 235]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 249]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 337]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 339]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 356]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 359]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 361]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 363]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 413]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 414]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 477]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 478]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 479])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 483])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup188 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions188⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields188 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 326])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 165]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 181]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 233]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 235]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 249]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 337]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 339]), (.Product #[.Constant ⟨⟨134217727, by decide⟩⟩, .Var 356]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 359]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 361]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 363]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 413]), (.Product #[.Constant ⟨⟨536870908, by decide⟩⟩, .Var 414]), (.Product #[.Constant ⟨⟨16777216, by decide⟩⟩, .Var 477]), (.Product #[.Constant ⟨⟨1996488705, by decide⟩⟩, .Var 478]), (.Product #[.Constant ⟨⟨1744831011, by decide⟩⟩, .Var 479])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 483])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1073741816, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values188 (logical : Nat → F) :
    (sourceExpressions188.map (Verification.environment logical)).toList = sourceFields188 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag188 (logical : Nat → F) :
    ((sourceFields188 logical)[5]?).getD 0 ≠ 0 := by
  change (4 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics188 (logical : Nat → F) :
    (sourceLookup188).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields188 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions188.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values188]
    exact source_tag188 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions188 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values188 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values188 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand189 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 352))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 346))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 355))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 100⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions189 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 491])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 485])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 494])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup189 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions189⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields189 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 491])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 485])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 494])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values189 (logical : Nat → F) :
    (sourceExpressions189.map (Verification.environment logical)).toList = sourceFields189 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag189 (logical : Nat → F) :
    ((sourceFields189 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics189 (logical : Nat → F) :
    (sourceLookup189).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields189 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions189.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values189]
    exact source_tag189 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions189 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values189 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values189 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand190 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 354))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 349))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 356))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1342177238, by decide⟩⟩⟩], 101⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions190 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 493])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 488])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 495])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)]), Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup190 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions190⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields190 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 493])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 488])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 495])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩)])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1342177238, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values190 (logical : Nat → F) :
    (sourceExpressions190.map (Verification.environment logical)).toList = sourceFields190 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag190 (logical : Nat → F) :
    ((sourceFields190 logical)[5]?).getD 0 ≠ 0 := by
  change (20 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics190 (logical : Nat → F) :
    (sourceLookup190).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields190 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions190.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values190]
    exact source_tag190 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions190 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values190 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values190 logical).trans same⟩

/-- One actual resolved primitive operand. -/
noncomputable def operand191 : NativeLookups.Operand := ⟨.one, .vector ⟨#[⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 273)), (⟨⟨536870912, by decide⟩⟩, (.BaseLayerWitness 276)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 351)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 352))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 353))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 47)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 125)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 126)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 129)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 145)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 148)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 150)), (⟨⟨1048576, by decide⟩⟩, (.BaseLayerWitness 343)), (⟨⟨268435456, by decide⟩⟩, (.BaseLayerWitness 344)), (⟨⟨2012217345, by decide⟩⟩, (.BaseLayerWitness 345)), (⟨⟨2004877313, by decide⟩⟩, (.BaseLayerWitness 346)), (⟨⟨1744830499, by decide⟩⟩, (.BaseLayerWitness 347))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 348))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[(⟨⟨268435454, by decide⟩⟩, (.BaseLayerWitness 357))], ⟨⟨0, by decide⟩⟩⟩, ⟨#[], ⟨⟨1207959431, by decide⟩⟩⟩], 102⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions191 : Vector (Airbender.Expression F) 6 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 412]), (.Product #[.Constant ⟨⟨536870912, by decide⟩⟩, .Var 415]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 490]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 491])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 492])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 186]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 264]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 265]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 268]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 284]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 287]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 289]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 482]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 483]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 484]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 485]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 486])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 487])]), Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 496])]), Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup191 : Lookup F := ⟨(WorkerConstraints.setupTable .blakeRound).toRaw, sourceExpressions191⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields191 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 412]), (.Product #[.Constant ⟨⟨536870912, by decide⟩⟩, .Var 415]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 490]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 491])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 492])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 186]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 264]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 265]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 268]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 284]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 287]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 289]), (.Product #[.Constant ⟨⟨1048576, by decide⟩⟩, .Var 482]), (.Product #[.Constant ⟨⟨268435456, by decide⟩⟩, .Var 483]), (.Product #[.Constant ⟨⟨2012217345, by decide⟩⟩, .Var 484]), (.Product #[.Constant ⟨⟨2004877313, by decide⟩⟩, .Var 485]), (.Product #[.Constant ⟨⟨1744830499, by decide⟩⟩, .Var 486])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 487])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 496])])).eval (Verification.environment logical), (Import.expression (.Sum #[(.Constant ⟨⟨1207959431, by decide⟩⟩)])).eval (Verification.environment logical)]

theorem source_values191 (logical : Nat → F) :
    (sourceExpressions191.map (Verification.environment logical)).toList = sourceFields191 logical := by kernel_rfl

/-- The fixed nonzero tag excludes native zero padding. -/
theorem source_tag191 (logical : Nat → F) :
    ((sourceFields191 logical)[5]?).getD 0 ≠ 0 := by
  change (57 : F) ≠ 0
  decide +kernel

/-- The reviewed query and public native table have the same members. -/
theorem source_semantics191 (logical : Nat → F) :
    (sourceLookup191).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields191 logical = NativeWorkerSetup.rows .blakeRound 0 index := by
  have tag : (((sourceExpressions191.map (Verification.environment logical)).toList)[width .blakeRound - 1]?).getD 0 ≠ 0 := by
    rw [source_values191]
    exact source_tag191 logical
  have equivalent := generic_lookup_refinement .blakeRound sourceExpressions191 logical tag
  constructor
  · intro accepted
    obtain ⟨index, same⟩ := equivalent.mp accepted
    exact ⟨index, (source_values191 logical).symm.trans same⟩
  · rintro ⟨index, same⟩
    exact equivalent.mpr ⟨index, (source_values191 logical).trans same⟩


end Airbender.Compiler.WorkerConstraints.BlakeRound
