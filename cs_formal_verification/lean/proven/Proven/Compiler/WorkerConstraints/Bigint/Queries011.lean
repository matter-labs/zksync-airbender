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
noncomputable def operand132 : NativeLookups.Operand := ⟨.one, .address (.InnerLayer 1 36)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions132 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 209])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup132 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions132⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields132 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 209])])).eval (Verification.environment logical)]

theorem source_values132 (logical : Nat → F) :
    (sourceExpressions132.map (Verification.environment logical)).toList = sourceFields132 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics132 (logical : Nat → F) :
    (sourceLookup132).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields132 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup132, sourceExpressions132, sourceFields132, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 209])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand133 : NativeLookups.Operand := ⟨.one, .address (.BaseLayerWitness 103)⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions133 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 162])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup133 : Lookup F := ⟨(Verification.range16Table).toRaw, sourceExpressions133⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields133 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 162])])).eval (Verification.environment logical)]

theorem source_values133 (logical : Nat → F) :
    (sourceExpressions133.map (Verification.environment logical)).toList = sourceFields133 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics133 (logical : Nat → F) :
    (sourceLookup133).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields133 logical = NativeWorkerSetup.rows .bigint 1 index := by
  simpa only [sourceLookup133, sourceExpressions133, sourceFields133, Verification.range16] using
    range16_refinement .bigint (Import.expression (.Sum #[(.Constant ⟨⟨0, by decide⟩⟩), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 162])])) logical


end Airbender.Compiler.WorkerConstraints.Bigint
