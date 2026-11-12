module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.Unified
public import Proven.GKRProtocol.CleanArithmeticNative.UnifiedCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.Unified
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 64. -/
theorem gate64 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate64.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate64.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨64, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate64 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[75]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨75, by decide⟩))

/-- The actual native sparse relation supplies gate 65. -/
theorem gate65 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate65.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate65.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨65, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate65 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[76]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨76, by decide⟩))

/-- The actual native sparse relation supplies gate 66. -/
theorem gate66 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate66.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate66.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨66, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate66 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[77]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨77, by decide⟩))

/-- The actual native sparse relation supplies gate 67. -/
theorem gate67 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate67.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate67.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨67, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate67 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[78]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨78, by decide⟩))

/-- The actual native sparse relation supplies gate 68. -/
theorem gate68 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate68.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate68.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨68, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate68 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[79]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨79, by decide⟩))

/-- The actual native sparse relation supplies gate 69. -/
theorem gate69 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate69.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate69.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨69, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate69 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[80]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨80, by decide⟩))

/-- The actual native sparse relation supplies gate 70. -/
theorem gate70 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate70.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate70.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨70, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate70 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[81]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨81, by decide⟩))

/-- The actual native sparse relation supplies gate 71. -/
theorem gate71 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate71.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate71.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨71, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate71 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[82]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨82, by decide⟩))

/-- The actual native sparse relation supplies gate 72. -/
theorem gate72 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate72.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate72.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨72, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate72 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[83]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨83, by decide⟩))

/-- The actual native sparse relation supplies gate 73. -/
theorem gate73 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate73.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate73.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨73, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate73 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[84]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨84, by decide⟩))

/-- The actual native sparse relation supplies gate 74. -/
theorem gate74 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate74.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate74.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨74, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate74 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[85]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨85, by decide⟩))

/-- The actual native sparse relation supplies gate 75. -/
theorem gate75 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate75.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate75.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨75, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate75 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[86]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨86, by decide⟩))

/-- The actual native sparse relation supplies gate 76. -/
theorem gate76 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate76.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate76.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨76, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate76 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[87]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨87, by decide⟩))

/-- The actual native sparse relation supplies gate 77. -/
theorem gate77 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate77.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate77.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨77, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate77 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[88]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨88, by decide⟩))

/-- The actual native sparse relation supplies gate 78. -/
theorem gate78 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate78.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate78.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨78, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate78 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[89]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨89, by decide⟩))

/-- The actual native sparse relation supplies gate 79. -/
theorem gate79 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate79.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate79.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨79, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate79 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[90]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨90, by decide⟩))

/-- This batch retains every native scalar equation at these positions. -/
theorem gates004 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate64, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate65, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate66, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate67, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate68, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate69, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate70, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate71, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate72, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate73, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate74, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate75, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate76, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate77, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate78, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate79], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 :=
  (cons_holds (gate64 physical accepted) (cons_holds (gate65 physical accepted) (cons_holds (gate66 physical accepted) (cons_holds (gate67 physical accepted) (cons_holds (gate68 physical accepted) (cons_holds (gate69 physical accepted) (cons_holds (gate70 physical accepted) (cons_holds (gate71 physical accepted) (cons_holds (gate72 physical accepted) (cons_holds (gate73 physical accepted) (cons_holds (gate74 physical accepted) (cons_holds (gate75 physical accepted) (cons_holds (gate76 physical accepted) (cons_holds (gate77 physical accepted) (cons_holds (gate78 physical accepted) (cons_holds (gate79 physical accepted) (by intro gate member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.Unified
