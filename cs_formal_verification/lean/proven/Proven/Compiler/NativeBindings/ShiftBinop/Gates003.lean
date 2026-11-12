module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.ShiftBinop
public import Proven.GKRProtocol.CleanArithmeticNative.ShiftBinopCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.ShiftBinop
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 48. -/
theorem gate48 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate48.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate48.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨48, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate48 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[51]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨51, by decide⟩))

/-- The actual native sparse relation supplies gate 49. -/
theorem gate49 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate49.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate49.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨49, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate49 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[53]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨53, by decide⟩))

/-- The actual native sparse relation supplies gate 50. -/
theorem gate50 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate50.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate50.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨50, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate50 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[54]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨54, by decide⟩))

/-- The actual native sparse relation supplies gate 51. -/
theorem gate51 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate51.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate51.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨51, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate51 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[55]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨55, by decide⟩))

/-- The actual native sparse relation supplies gate 52. -/
theorem gate52 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate52.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate52.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨52, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate52 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[56]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨56, by decide⟩))

/-- The actual native sparse relation supplies gate 53. -/
theorem gate53 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate53.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate53.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨53, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate53 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[57]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨57, by decide⟩))

/-- The actual native sparse relation supplies gate 54. -/
theorem gate54 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate54.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate54.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨54, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate54 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[58]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨58, by decide⟩))

/-- The actual native sparse relation supplies gate 55. -/
theorem gate55 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate55.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate55.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨55, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate55 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[59]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨59, by decide⟩))

/-- The actual native sparse relation supplies gate 56. -/
theorem gate56 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate56.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate56.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨56, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate56 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[60]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨60, by decide⟩))

/-- The actual native sparse relation supplies gate 57. -/
theorem gate57 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate57.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate57.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨57, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate57 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[61]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨61, by decide⟩))

/-- The actual native sparse relation supplies gate 58. -/
theorem gate58 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate58.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate58.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨58, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate58 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[62]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨62, by decide⟩))

/-- The actual native sparse relation supplies gate 59. -/
theorem gate59 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate59.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate59.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨59, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate59 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[63]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨63, by decide⟩))

/-- The actual native sparse relation supplies gate 60. -/
theorem gate60 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate60.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate60.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨60, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate60 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[64]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨64, by decide⟩))

/-- The actual native sparse relation supplies gate 61. -/
theorem gate61 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate61.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate61.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gatesChecked _ (List.get_mem _ ⟨61, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate61 (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.ShiftBinop.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨0, by decide⟩))

/-- This batch retains every native scalar equation at these positions. -/
theorem gates003 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate48, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate49, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate50, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate51, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate52, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate53, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate54, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate55, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate56, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate57, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate58, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate59, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate60, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.gate61], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0 :=
  (cons_holds (gate48 physical accepted) (cons_holds (gate49 physical accepted) (cons_holds (gate50 physical accepted) (cons_holds (gate51 physical accepted) (cons_holds (gate52 physical accepted) (cons_holds (gate53 physical accepted) (cons_holds (gate54 physical accepted) (cons_holds (gate55 physical accepted) (cons_holds (gate56 physical accepted) (cons_holds (gate57 physical accepted) (cons_holds (gate58 physical accepted) (cons_holds (gate59 physical accepted) (cons_holds (gate60 physical accepted) (cons_holds (gate61 physical accepted) (by intro gate member; cases member)))))))))))))))
end Airbender.Compiler.NativeBindings.ShiftBinop
