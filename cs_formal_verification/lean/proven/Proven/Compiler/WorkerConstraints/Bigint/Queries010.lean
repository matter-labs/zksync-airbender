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
noncomputable def operand120 : NativeLookups.Operand := ⟨.one, .address (.InnerLayer 1 24)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions120 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 197])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup120 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions120⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields120 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 197])])).eval (Verification.environment logical)]

theorem source_values120 (logical : Nat → F) :
    (sourceExpressions120.map (Verification.environment logical)).toList = sourceFields120 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics120 (logical : Nat → F) :
    (sourceLookup120).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields120 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup120, sourceExpressions120, sourceFields120, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 197])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand121 : NativeLookups.Operand := ⟨.one, .address (.InnerLayer 1 25)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions121 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 198])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup121 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions121⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields121 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 198])])).eval (Verification.environment logical)]

theorem source_values121 (logical : Nat → F) :
    (sourceExpressions121.map (Verification.environment logical)).toList = sourceFields121 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics121 (logical : Nat → F) :
    (sourceLookup121).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields121 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup121, sourceExpressions121, sourceFields121, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 198])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand122 : NativeLookups.Operand := ⟨.one, .address (.InnerLayer 1 26)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions122 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 199])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup122 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions122⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields122 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 199])])).eval (Verification.environment logical)]

theorem source_values122 (logical : Nat → F) :
    (sourceExpressions122.map (Verification.environment logical)).toList = sourceFields122 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics122 (logical : Nat → F) :
    (sourceLookup122).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields122 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup122, sourceExpressions122, sourceFields122, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 199])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand123 : NativeLookups.Operand := ⟨.one, .address (.InnerLayer 1 27)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions123 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 200])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup123 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions123⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields123 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 200])])).eval (Verification.environment logical)]

theorem source_values123 (logical : Nat → F) :
    (sourceExpressions123.map (Verification.environment logical)).toList = sourceFields123 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics123 (logical : Nat → F) :
    (sourceLookup123).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields123 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup123, sourceExpressions123, sourceFields123, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 200])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand124 : NativeLookups.Operand := ⟨.one, .address (.InnerLayer 1 28)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions124 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 201])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup124 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions124⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields124 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 201])])).eval (Verification.environment logical)]

theorem source_values124 (logical : Nat → F) :
    (sourceExpressions124.map (Verification.environment logical)).toList = sourceFields124 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics124 (logical : Nat → F) :
    (sourceLookup124).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields124 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup124, sourceExpressions124, sourceFields124, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 201])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand125 : NativeLookups.Operand := ⟨.one, .address (.InnerLayer 1 29)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions125 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 202])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup125 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions125⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields125 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 202])])).eval (Verification.environment logical)]

theorem source_values125 (logical : Nat → F) :
    (sourceExpressions125.map (Verification.environment logical)).toList = sourceFields125 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics125 (logical : Nat → F) :
    (sourceLookup125).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields125 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup125, sourceExpressions125, sourceFields125, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 202])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand126 : NativeLookups.Operand := ⟨.one, .address (.InnerLayer 1 30)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions126 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 203])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup126 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions126⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields126 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 203])])).eval (Verification.environment logical)]

theorem source_values126 (logical : Nat → F) :
    (sourceExpressions126.map (Verification.environment logical)).toList = sourceFields126 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics126 (logical : Nat → F) :
    (sourceLookup126).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields126 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup126, sourceExpressions126, sourceFields126, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 203])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand127 : NativeLookups.Operand := ⟨.one, .address (.InnerLayer 1 31)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions127 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 204])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup127 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions127⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields127 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 204])])).eval (Verification.environment logical)]

theorem source_values127 (logical : Nat → F) :
    (sourceExpressions127.map (Verification.environment logical)).toList = sourceFields127 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics127 (logical : Nat → F) :
    (sourceLookup127).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields127 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup127, sourceExpressions127, sourceFields127, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 204])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand128 : NativeLookups.Operand := ⟨.one, .address (.InnerLayer 1 32)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions128 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 205])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup128 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions128⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields128 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 205])])).eval (Verification.environment logical)]

theorem source_values128 (logical : Nat → F) :
    (sourceExpressions128.map (Verification.environment logical)).toList = sourceFields128 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics128 (logical : Nat → F) :
    (sourceLookup128).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields128 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup128, sourceExpressions128, sourceFields128, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 205])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand129 : NativeLookups.Operand := ⟨.one, .address (.InnerLayer 1 33)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions129 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 206])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup129 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions129⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields129 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 206])])).eval (Verification.environment logical)]

theorem source_values129 (logical : Nat → F) :
    (sourceExpressions129.map (Verification.environment logical)).toList = sourceFields129 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics129 (logical : Nat → F) :
    (sourceLookup129).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields129 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup129, sourceExpressions129, sourceFields129, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 206])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand130 : NativeLookups.Operand := ⟨.one, .address (.InnerLayer 1 34)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions130 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 207])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup130 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions130⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields130 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 207])])).eval (Verification.environment logical)]

theorem source_values130 (logical : Nat → F) :
    (sourceExpressions130.map (Verification.environment logical)).toList = sourceFields130 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics130 (logical : Nat → F) :
    (sourceLookup130).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields130 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup130, sourceExpressions130, sourceFields130, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 207])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand131 : NativeLookups.Operand := ⟨.one, .address (.InnerLayer 1 35)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions131 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 208])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup131 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions131⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields131 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 208])])).eval (Verification.environment logical)]

theorem source_values131 (logical : Nat → F) :
    (sourceExpressions131.map (Verification.environment logical)).toList = sourceFields131 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics131 (logical : Nat → F) :
    (sourceLookup131).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields131 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup131, sourceExpressions131, sourceFields131, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 208])])) logical


end Airbender.Compiler.WorkerConstraints.Bigint
