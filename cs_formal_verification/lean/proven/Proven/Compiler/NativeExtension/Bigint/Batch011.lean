module
public import Proven.Compiler.Reverse
public import Proven.Compiler.NativeBindings.Bigint
public import Proven.KernelExact

@[expose] public section
namespace Airbender.Compiler.NativeExtension.Bigint
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse176 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate176.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨176, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate176 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨176, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse177 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[54]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate177.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨177, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate177 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[54]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨177, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse178 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[55]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate178.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨178, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate178 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[55]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨178, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse179 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[2]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[2]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate179.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨179, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate179 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[2]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[2]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨179, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse180 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[3]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[3]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate180.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨180, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate180 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[3]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[3]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨180, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse181 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[4]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[4]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate181.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨181, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate181 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[4]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[4]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨181, by decide⟩)))

theorem batch011 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    ∀ clause ∈ [(Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[54]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[55]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[2]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[2]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[3]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[3]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[4]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[4]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (reverse176 physical holds) (cons_zero (reverse177 physical holds) (cons_zero (reverse178 physical holds) (cons_zero (reverse179 physical holds) (cons_zero (reverse180 physical holds) (cons_zero (reverse181 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)))))))
end Airbender.Compiler.NativeExtension.Bigint
