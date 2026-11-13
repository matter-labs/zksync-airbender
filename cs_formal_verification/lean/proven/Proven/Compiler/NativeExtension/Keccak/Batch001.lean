module
public import Proven.Compiler.Reverse
public import Proven.Compiler.NativeBindings.Keccak
public import Proven.KernelExact

@[expose] public section
namespace Airbender.Compiler.NativeExtension.Keccak
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse16 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[46]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[46]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate16.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨16, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate16 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[46]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[46]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨16, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse17 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[47]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[47]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate17.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨17, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate17 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[47]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[47]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨17, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse18 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[48]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[48]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate18.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨18, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate18 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[48]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[48]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨18, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse19 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[49]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[49]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate19.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨19, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate19 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[49]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[49]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨19, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse20 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[50]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[50]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate20.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨20, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate20 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[50]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[50]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨20, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse21 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[51]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[51]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate21.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨21, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate21 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[51]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[51]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨21, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse22 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[52]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[52]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate22.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨22, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate22 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[52]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[52]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨22, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse23 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[53]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[53]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate23.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨23, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate23 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[53]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[53]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨23, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse24 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[54]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[54]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate24.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨24, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate24 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[54]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[54]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨24, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse25 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[55]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[55]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate25.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨25, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate25 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[55]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[55]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨25, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse26 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[56]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[56]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate26.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨26, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate26 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[56]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[56]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨26, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse27 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[57]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[57]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate27.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨27, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate27 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[57]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[57]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨27, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse28 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[58]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[58]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate28.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨28, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate28 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[58]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[58]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨28, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse29 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[59]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[59]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate29.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨29, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate29 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[59]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[59]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨29, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse30 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate30.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨30, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate30 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨30, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse31 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[32]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate31.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨31, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate31 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[32]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨31, by decide⟩)))

theorem batch001 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) :
    ∀ clause ∈ [(Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[46]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[46]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[47]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[47]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[48]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[48]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[49]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[49]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[50]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[50]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[51]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[51]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[52]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[52]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[53]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[53]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[54]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[54]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[55]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[55]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[56]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[56]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[57]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[57]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[58]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[58]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[59]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[59]'(by decide)).2), (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[32]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (reverse16 physical holds) (cons_zero (reverse17 physical holds) (cons_zero (reverse18 physical holds) (cons_zero (reverse19 physical holds) (cons_zero (reverse20 physical holds) (cons_zero (reverse21 physical holds) (cons_zero (reverse22 physical holds) (cons_zero (reverse23 physical holds) (cons_zero (reverse24 physical holds) (cons_zero (reverse25 physical holds) (cons_zero (reverse26 physical holds) (cons_zero (reverse27 physical holds) (cons_zero (reverse28 physical holds) (cons_zero (reverse29 physical holds) (cons_zero (reverse30 physical holds) (cons_zero (reverse31 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)))))))))))))))))
end Airbender.Compiler.NativeExtension.Keccak
