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
theorem reverse16 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[56]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[56]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate16.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨16, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate16 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[56]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[56]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨16, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse17 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[57]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[57]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate17.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨17, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate17 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[57]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[57]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨17, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse18 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[58]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[58]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate18.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨18, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate18 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[58]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[58]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨18, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse19 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[59]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[59]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate19.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨19, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate19 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[59]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[59]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨19, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse20 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[60]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[60]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate20.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨20, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate20 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[60]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[60]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨20, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse21 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[61]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[61]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate21.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨21, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate21 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[61]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[61]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨21, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse22 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[62]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[62]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate22.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨22, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate22 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[62]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[62]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨22, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse23 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[63]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[63]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate23.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨23, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate23 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[63]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[63]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨23, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse24 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[64]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[64]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate24.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨24, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate24 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[64]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[64]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨24, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse25 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[65]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[65]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate25.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨25, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate25 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[65]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[65]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨25, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse26 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[66]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[66]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate26.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨26, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate26 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[66]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[66]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨26, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse27 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[67]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[67]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate27.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨27, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate27 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[67]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[67]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨27, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse28 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[68]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[68]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate28.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨28, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate28 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[68]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[68]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨28, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse29 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[69]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[69]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate29.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨29, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate29 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[69]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[69]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨29, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse30 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[70]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[70]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate30.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨30, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate30 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[70]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[70]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨30, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse31 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[71]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[71]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate31.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨31, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate31 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[71]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[71]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨31, by decide⟩)))

theorem batch001 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    ∀ clause ∈ [(Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[56]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[56]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[57]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[57]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[58]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[58]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[59]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[59]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[60]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[60]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[61]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[61]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[62]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[62]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[63]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[63]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[64]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[64]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[65]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[65]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[66]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[66]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[67]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[67]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[68]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[68]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[69]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[69]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[70]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[70]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[71]'(by decide)).1 (((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).cached_relations[71]'(by decide)).2)], clause.residual physical = 0 :=
  (cons_zero (reverse16 physical holds) (cons_zero (reverse17 physical holds) (cons_zero (reverse18 physical holds) (cons_zero (reverse19 physical holds) (cons_zero (reverse20 physical holds) (cons_zero (reverse21 physical holds) (cons_zero (reverse22 physical holds) (cons_zero (reverse23 physical holds) (cons_zero (reverse24 physical holds) (cons_zero (reverse25 physical holds) (cons_zero (reverse26 physical holds) (cons_zero (reverse27 physical holds) (cons_zero (reverse28 physical holds) (cons_zero (reverse29 physical holds) (cons_zero (reverse30 physical holds) (cons_zero (reverse31 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)))))))))))))))))
end Airbender.Compiler.NativeExtension.Bigint
