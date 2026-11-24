module
public import Proven.Compiler.WorkerConstraints.Values
public import Proven.Compiler.WorkerConstraints.Setup
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One actual resolved primitive operand. -/
noncomputable def operand0 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 88)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions0 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 147])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup0 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions0⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields0 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 147])])).eval (Verification.environment logical)]

theorem source_values0 (logical : Nat → F) :
    (sourceExpressions0.map (Verification.environment logical)).toList = sourceFields0 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics0 (logical : Nat → F) :
    (sourceLookup0).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields0 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup0, sourceExpressions0, sourceFields0, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 147])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand1 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 89)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions1 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 148])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup1 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions1⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields1 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 148])])).eval (Verification.environment logical)]

theorem source_values1 (logical : Nat → F) :
    (sourceExpressions1.map (Verification.environment logical)).toList = sourceFields1 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics1 (logical : Nat → F) :
    (sourceLookup1).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields1 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup1, sourceExpressions1, sourceFields1, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 148])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand2 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 90)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions2 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 149])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup2 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions2⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields2 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 149])])).eval (Verification.environment logical)]

theorem source_values2 (logical : Nat → F) :
    (sourceExpressions2.map (Verification.environment logical)).toList = sourceFields2 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics2 (logical : Nat → F) :
    (sourceLookup2).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields2 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup2, sourceExpressions2, sourceFields2, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 149])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand3 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 91)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions3 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 150])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup3 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions3⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields3 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 150])])).eval (Verification.environment logical)]

theorem source_values3 (logical : Nat → F) :
    (sourceExpressions3.map (Verification.environment logical)).toList = sourceFields3 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics3 (logical : Nat → F) :
    (sourceLookup3).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields3 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup3, sourceExpressions3, sourceFields3, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 150])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand4 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 92)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions4 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 151])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup4 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions4⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields4 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 151])])).eval (Verification.environment logical)]

theorem source_values4 (logical : Nat → F) :
    (sourceExpressions4.map (Verification.environment logical)).toList = sourceFields4 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics4 (logical : Nat → F) :
    (sourceLookup4).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields4 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup4, sourceExpressions4, sourceFields4, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 151])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand5 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 93)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions5 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 152])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup5 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions5⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields5 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 152])])).eval (Verification.environment logical)]

theorem source_values5 (logical : Nat → F) :
    (sourceExpressions5.map (Verification.environment logical)).toList = sourceFields5 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics5 (logical : Nat → F) :
    (sourceLookup5).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields5 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup5, sourceExpressions5, sourceFields5, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 152])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand6 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 94)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions6 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 153])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup6 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions6⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields6 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 153])])).eval (Verification.environment logical)]

theorem source_values6 (logical : Nat → F) :
    (sourceExpressions6.map (Verification.environment logical)).toList = sourceFields6 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics6 (logical : Nat → F) :
    (sourceLookup6).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields6 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup6, sourceExpressions6, sourceFields6, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 153])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand7 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 95)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions7 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 154])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup7 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions7⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields7 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 154])])).eval (Verification.environment logical)]

theorem source_values7 (logical : Nat → F) :
    (sourceExpressions7.map (Verification.environment logical)).toList = sourceFields7 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics7 (logical : Nat → F) :
    (sourceLookup7).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields7 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup7, sourceExpressions7, sourceFields7, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 154])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand8 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 96)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions8 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 155])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup8 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions8⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields8 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 155])])).eval (Verification.environment logical)]

theorem source_values8 (logical : Nat → F) :
    (sourceExpressions8.map (Verification.environment logical)).toList = sourceFields8 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics8 (logical : Nat → F) :
    (sourceLookup8).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields8 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup8, sourceExpressions8, sourceFields8, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 155])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand9 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 97)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions9 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 156])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup9 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions9⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields9 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 156])])).eval (Verification.environment logical)]

theorem source_values9 (logical : Nat → F) :
    (sourceExpressions9.map (Verification.environment logical)).toList = sourceFields9 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics9 (logical : Nat → F) :
    (sourceLookup9).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields9 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup9, sourceExpressions9, sourceFields9, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 156])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand10 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 98)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions10 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 157])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup10 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions10⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields10 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 157])])).eval (Verification.environment logical)]

theorem source_values10 (logical : Nat → F) :
    (sourceExpressions10.map (Verification.environment logical)).toList = sourceFields10 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics10 (logical : Nat → F) :
    (sourceLookup10).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields10 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup10, sourceExpressions10, sourceFields10, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 157])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand11 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 99)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions11 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 158])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup11 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions11⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields11 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 158])])).eval (Verification.environment logical)]

theorem source_values11 (logical : Nat → F) :
    (sourceExpressions11.map (Verification.environment logical)).toList = sourceFields11 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics11 (logical : Nat → F) :
    (sourceLookup11).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields11 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup11, sourceExpressions11, sourceFields11, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 158])])) logical


end Airbender.Compiler.WorkerConstraints.Bigint
