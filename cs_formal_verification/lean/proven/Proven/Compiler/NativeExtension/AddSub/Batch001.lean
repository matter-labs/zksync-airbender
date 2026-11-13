module
public import Proven.Compiler.Reverse
public import Proven.Compiler.NativeBindings.AddSub
public import Proven.KernelExact

@[expose] public section
namespace Airbender.Compiler.NativeExtension.AddSub
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse16 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[22]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate16.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨16, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate16 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[22]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨16, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse17 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[23]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate17.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨17, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate17 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[23]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨17, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse18 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[24]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate18.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨18, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate18 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[24]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨18, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse19 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[25]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate19.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨19, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate19 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[25]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨19, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse20 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[26]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate20.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨20, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate20 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[26]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨20, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse21 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[27]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate21.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨21, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate21 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[27]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨21, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse22 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[28]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate22.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨22, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate22 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[28]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨22, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse23 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[29]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate23.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨23, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate23 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[29]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨23, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse24 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[30]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate24.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨24, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate24 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[30]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨24, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse25 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[31]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate25.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨25, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate25 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[31]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨25, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse26 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[32]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate26.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨26, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate26 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[32]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨26, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse27 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[33]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate27.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨27, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate27 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[33]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨27, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse28 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[34]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate28.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨28, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate28 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[34]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨28, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse29 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[35]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate29.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨29, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate29 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[35]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨29, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse30 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[36]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate30.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨30, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate30 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[36]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨30, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse31 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[37]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate31.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gatesChecked _ (List.get_mem _ ⟨31, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate31 (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[37]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨31, by decide⟩)))

theorem batch001 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    ∀ clause ∈ [(Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[22]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[23]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[24]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[25]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[26]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[27]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[28]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[29]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[30]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[31]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[32]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[33]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[34]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[35]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[36]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.AddSub.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[37]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (reverse16 physical holds) (cons_zero (reverse17 physical holds) (cons_zero (reverse18 physical holds) (cons_zero (reverse19 physical holds) (cons_zero (reverse20 physical holds) (cons_zero (reverse21 physical holds) (cons_zero (reverse22 physical holds) (cons_zero (reverse23 physical holds) (cons_zero (reverse24 physical holds) (cons_zero (reverse25 physical holds) (cons_zero (reverse26 physical holds) (cons_zero (reverse27 physical holds) (cons_zero (reverse28 physical holds) (cons_zero (reverse29 physical holds) (cons_zero (reverse30 physical holds) (cons_zero (reverse31 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)))))))))))))))))
end Airbender.Compiler.NativeExtension.AddSub
