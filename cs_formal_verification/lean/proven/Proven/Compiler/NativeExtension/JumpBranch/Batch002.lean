module
public import Proven.Compiler.Reverse
public import Proven.Compiler.NativeBindings.JumpBranch
public import Proven.KernelExact

@[expose] public section
namespace Airbender.Compiler.NativeExtension.JumpBranch
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse32 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[39]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate32.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gatesChecked _ (List.get_mem _ ⟨32, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate32 (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[39]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨32, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse33 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[40]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate33.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gatesChecked _ (List.get_mem _ ⟨33, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate33 (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[40]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨33, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse34 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[41]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate34.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gatesChecked _ (List.get_mem _ ⟨34, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate34 (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[41]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨34, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse35 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate35.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gatesChecked _ (List.get_mem _ ⟨35, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.gate35 (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨35, by decide⟩)))

theorem batch002 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0) :
    ∀ clause ∈ [(Clause.gate ((((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[39]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[40]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[41]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.JumpBranch.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (reverse32 physical holds) (cons_zero (reverse33 physical holds) (cons_zero (reverse34 physical holds) (cons_zero (reverse35 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)))))
end Airbender.Compiler.NativeExtension.JumpBranch
