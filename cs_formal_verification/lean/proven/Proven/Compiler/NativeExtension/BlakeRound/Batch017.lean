module
public import Proven.Compiler.Reverse
public import Proven.Compiler.NativeBindings.BlakeRound
public import Proven.KernelExact

@[expose] public section
namespace Airbender.Compiler.NativeExtension.BlakeRound
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse272 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[369]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate272.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨272, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate272 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[369]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨272, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse273 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[370]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate273.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨273, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate273 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[370]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨273, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse274 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[371]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate274.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨274, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate274 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[371]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨274, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse275 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[372]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate275.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨275, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate275 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[372]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨275, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse276 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[373]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate276.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨276, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate276 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[373]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨276, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse277 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[374]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate277.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨277, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate277 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[374]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨277, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse278 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[375]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate278.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨278, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate278 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[375]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨278, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse279 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[376]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate279.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨279, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate279 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[376]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨279, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse280 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[377]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate280.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨280, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate280 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[377]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨280, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse281 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[378]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate281.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨281, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate281 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[378]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨281, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse282 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[379]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate282.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨282, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate282 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[379]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨282, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse283 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[380]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate283.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨283, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate283 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[380]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨283, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse284 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[381]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate284.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨284, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate284 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[381]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨284, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse285 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[382]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate285.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨285, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate285 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[382]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨285, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse286 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[383]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate286.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨286, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate286 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[383]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨286, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse287 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[384]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate287.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨287, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate287 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[384]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨287, by decide⟩)))

theorem batch017 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    ∀ clause ∈ [(Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[369]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[370]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[371]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[372]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[373]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[374]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[375]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[376]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[377]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[378]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[379]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[380]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[381]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[382]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[383]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[384]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (reverse272 physical holds) (cons_zero (reverse273 physical holds) (cons_zero (reverse274 physical holds) (cons_zero (reverse275 physical holds) (cons_zero (reverse276 physical holds) (cons_zero (reverse277 physical holds) (cons_zero (reverse278 physical holds) (cons_zero (reverse279 physical holds) (cons_zero (reverse280 physical holds) (cons_zero (reverse281 physical holds) (cons_zero (reverse282 physical holds) (cons_zero (reverse283 physical holds) (cons_zero (reverse284 physical holds) (cons_zero (reverse285 physical holds) (cons_zero (reverse286 physical holds) (cons_zero (reverse287 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)))))))))))))))))
end Airbender.Compiler.NativeExtension.BlakeRound
