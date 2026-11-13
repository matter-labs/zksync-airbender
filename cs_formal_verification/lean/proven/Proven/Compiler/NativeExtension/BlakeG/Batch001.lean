module
public import Proven.Compiler.Reverse
public import Proven.Compiler.NativeBindings.BlakeG
public import Proven.KernelExact

@[expose] public section
namespace Airbender.Compiler.NativeExtension.BlakeG
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse16 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[36]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[36]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate16.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨16, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate16 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[36]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[36]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨16, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse17 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[37]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[37]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate17.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨17, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate17 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[37]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[37]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨17, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse18 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[38]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[38]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate18.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨18, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate18 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[38]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[38]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨18, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse19 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[39]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[39]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate19.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨19, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate19 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[39]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[39]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨19, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse20 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[40]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[40]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate20.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨20, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate20 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[40]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[40]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨20, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse21 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate21.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨21, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate21 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨21, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse22 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[32]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate22.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨22, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate22 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[32]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨22, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse23 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[33]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate23.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨23, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate23 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[33]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨23, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse24 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[34]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate24.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨24, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate24 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[34]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨24, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse25 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[35]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate25.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨25, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate25 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[35]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨25, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse26 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[36]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate26.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨26, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate26 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[36]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨26, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse27 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[37]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate27.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨27, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate27 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[37]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨27, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse28 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[38]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate28.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨28, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate28 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[38]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨28, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse29 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[39]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate29.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨29, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate29 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[39]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨29, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse30 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[40]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate30.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨30, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate30 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[40]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨30, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse31 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[41]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate31.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨31, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate31 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[41]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨31, by decide⟩)))

theorem batch001 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    ∀ clause ∈ [(Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[36]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[36]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[37]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[37]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[38]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[38]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[39]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[39]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[40]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[40]'(by decide)).2), (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[32]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[33]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[34]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[35]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[36]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[37]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[38]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[39]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[40]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[41]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (reverse16 physical holds) (cons_zero (reverse17 physical holds) (cons_zero (reverse18 physical holds) (cons_zero (reverse19 physical holds) (cons_zero (reverse20 physical holds) (cons_zero (reverse21 physical holds) (cons_zero (reverse22 physical holds) (cons_zero (reverse23 physical holds) (cons_zero (reverse24 physical holds) (cons_zero (reverse25 physical holds) (cons_zero (reverse26 physical holds) (cons_zero (reverse27 physical holds) (cons_zero (reverse28 physical holds) (cons_zero (reverse29 physical holds) (cons_zero (reverse30 physical holds) (cons_zero (reverse31 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)))))))))))))))))
end Airbender.Compiler.NativeExtension.BlakeG
