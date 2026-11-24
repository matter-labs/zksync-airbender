module
public import Proven.Compiler.Reverse
public import Proven.Compiler.NativeBindings.Unified
public import Proven.KernelExact

@[expose] public section
namespace Airbender.Compiler.NativeExtension.Unified
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse64 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[75]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate64.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨64, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate64 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[75]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨64, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse65 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[76]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate65.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨65, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate65 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[76]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨65, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse66 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[77]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate66.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨66, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate66 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[77]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨66, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse67 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[78]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate67.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨67, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate67 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[78]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨67, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse68 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[79]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate68.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨68, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate68 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[79]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨68, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse69 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[80]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate69.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨69, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate69 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[80]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨69, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse70 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[81]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate70.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨70, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate70 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[81]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨70, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse71 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[82]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate71.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨71, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate71 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[82]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨71, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse72 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[83]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate72.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨72, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate72 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[83]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨72, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse73 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[84]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate73.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨73, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate73 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[84]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨73, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse74 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[85]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate74.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨74, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate74 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[85]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨74, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse75 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[86]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate75.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨75, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate75 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[86]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨75, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse76 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[87]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate76.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨76, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate76 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[87]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨76, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse77 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[88]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate77.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨77, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate77 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[88]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨77, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse78 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[89]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate78.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨78, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate78 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[89]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨78, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse79 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[90]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate79.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨79, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate79 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[90]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨79, by decide⟩)))

theorem batch004 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    ∀ clause ∈ [(Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[75]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[76]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[77]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[78]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[79]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[80]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[81]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[82]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[83]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[84]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[85]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[86]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[87]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[88]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[89]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[90]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (reverse64 physical holds) (cons_zero (reverse65 physical holds) (cons_zero (reverse66 physical holds) (cons_zero (reverse67 physical holds) (cons_zero (reverse68 physical holds) (cons_zero (reverse69 physical holds) (cons_zero (reverse70 physical holds) (cons_zero (reverse71 physical holds) (cons_zero (reverse72 physical holds) (cons_zero (reverse73 physical holds) (cons_zero (reverse74 physical holds) (cons_zero (reverse75 physical holds) (cons_zero (reverse76 physical holds) (cons_zero (reverse77 physical holds) (cons_zero (reverse78 physical holds) (cons_zero (reverse79 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)))))))))))))))))
end Airbender.Compiler.NativeExtension.Unified
