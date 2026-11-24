module
public import Proven.Compiler.Reverse
public import Proven.Compiler.NativeBindings.SubwordMemory
public import Proven.KernelExact

@[expose] public section
namespace Airbender.Compiler.NativeExtension.SubwordMemory
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse48 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[3]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate48.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨48, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate48 (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[3]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨48, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse49 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[4]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate49.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨49, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate49 (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[4]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨49, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse50 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[14]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate50.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨50, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate50 (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[14]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨50, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse51 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    (Clause.gate ((((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[15]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate51.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨51, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate51 (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[15]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨51, by decide⟩)))

theorem batch003 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0) :
    ∀ clause ∈ [(Clause.gate ((((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[3]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[4]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[14]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[15]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (reverse48 physical holds) (cons_zero (reverse49 physical holds) (cons_zero (reverse50 physical holds) (cons_zero (reverse51 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)))))
end Airbender.Compiler.NativeExtension.SubwordMemory
