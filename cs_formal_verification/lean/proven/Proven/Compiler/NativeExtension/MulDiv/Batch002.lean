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
theorem reverse32 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[42]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate32.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨32, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate32 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[42]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨32, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse33 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[43]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate33.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨33, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate33 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[43]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨33, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse34 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[44]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate34.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨34, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate34 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[44]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨34, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse35 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[45]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate35.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨35, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate35 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[45]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨35, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse36 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[46]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate36.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨36, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate36 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[46]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨36, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse37 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[47]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate37.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨37, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate37 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[47]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨37, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse38 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[48]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate38.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨38, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate38 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[48]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨38, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse39 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[49]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate39.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨39, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate39 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[49]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨39, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse40 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[50]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate40.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨40, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate40 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[50]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨40, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse41 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[51]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate41.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨41, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate41 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[51]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨41, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse42 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate42.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨42, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate42 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨42, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse43 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[14]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate43.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨43, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate43 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[14]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨43, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse44 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[15]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate44.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨44, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate44 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[15]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨44, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse45 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[16]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate45.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨45, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate45 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[16]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨45, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse46 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[17]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate46.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨46, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate46 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[17]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨46, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse47 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[18]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate47.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨47, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate47 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[18]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨47, by decide⟩)))

theorem batch002 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0) :
    ∀ clause ∈ [(Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[42]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[43]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[44]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[45]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[46]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[47]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[48]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[49]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[50]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[51]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[14]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[15]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[16]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[17]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[18]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (reverse32 physical holds) (cons_zero (reverse33 physical holds) (cons_zero (reverse34 physical holds) (cons_zero (reverse35 physical holds) (cons_zero (reverse36 physical holds) (cons_zero (reverse37 physical holds) (cons_zero (reverse38 physical holds) (cons_zero (reverse39 physical holds) (cons_zero (reverse40 physical holds) (cons_zero (reverse41 physical holds) (cons_zero (reverse42 physical holds) (cons_zero (reverse43 physical holds) (cons_zero (reverse44 physical holds) (cons_zero (reverse45 physical holds) (cons_zero (reverse46 physical holds) (cons_zero (reverse47 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)))))))))))))))))
end Airbender.Compiler.NativeExtension.MulDiv
