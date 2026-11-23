module
public import Proven.Compiler.Reverse
public import Proven.Compiler.NativeBindings.MulDiv
public import Proven.KernelExact

@[expose] public section
namespace Airbender.Compiler.NativeExtension.MulDiv
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse48 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[19]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate48.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨48, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate48 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[19]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨48, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse49 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[20]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate49.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨49, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate49 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[20]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨49, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse50 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[21]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate50.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨50, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate50 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[21]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨50, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse51 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[22]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate51.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨51, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate51 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[22]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨51, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse52 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[23]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate52.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨52, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate52 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[23]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨52, by decide⟩)))

theorem batch003 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    ∀ clause ∈ [(Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[19]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[20]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[21]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[22]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[23]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (reverse48 physical holds) (cons_zero (reverse49 physical holds) (cons_zero (reverse50 physical holds) (cons_zero (reverse51 physical holds) (cons_zero (reverse52 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member))))))
end Airbender.Compiler.NativeExtension.MulDiv
