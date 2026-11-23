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
theorem reverse144 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[183]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate144.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨144, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate144 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[183]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨144, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse145 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[184]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate145.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨145, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate145 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[184]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨145, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse146 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[185]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate146.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨146, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate146 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[185]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨146, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse147 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[186]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate147.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨147, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate147 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[186]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨147, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse148 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[187]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate148.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨148, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate148 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[187]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨148, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse149 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[188]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate149.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨149, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate149 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[188]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨149, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse150 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[189]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate150.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨150, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate150 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[189]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨150, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse151 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[190]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate151.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨151, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate151 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[190]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨151, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse152 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[191]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate152.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨152, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate152 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[191]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨152, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse153 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[192]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate153.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨153, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate153 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[192]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨153, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse154 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[193]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate154.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨154, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate154 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[193]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨154, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse155 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[194]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate155.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨155, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate155 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[194]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨155, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse156 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[195]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate156.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨156, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate156 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[195]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨156, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse157 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[196]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate157.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨157, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate157 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[196]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨157, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse158 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[197]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate158.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨158, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate158 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[197]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨158, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse159 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[198]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate159.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BigintCached.native.gatesChecked _ (List.get_mem _ ⟨159, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate159 (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[198]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨159, by decide⟩)))

theorem batch009 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    ∀ clause ∈ [(Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[183]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[184]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[185]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[186]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[187]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[188]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[189]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[190]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[191]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[192]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[193]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[194]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[195]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[196]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[197]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Bigint.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[198]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (reverse144 physical holds) (cons_zero (reverse145 physical holds) (cons_zero (reverse146 physical holds) (cons_zero (reverse147 physical holds) (cons_zero (reverse148 physical holds) (cons_zero (reverse149 physical holds) (cons_zero (reverse150 physical holds) (cons_zero (reverse151 physical holds) (cons_zero (reverse152 physical holds) (cons_zero (reverse153 physical holds) (cons_zero (reverse154 physical holds) (cons_zero (reverse155 physical holds) (cons_zero (reverse156 physical holds) (cons_zero (reverse157 physical holds) (cons_zero (reverse158 physical holds) (cons_zero (reverse159 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)))))))))))))))))
end Airbender.Compiler.NativeExtension.Bigint
