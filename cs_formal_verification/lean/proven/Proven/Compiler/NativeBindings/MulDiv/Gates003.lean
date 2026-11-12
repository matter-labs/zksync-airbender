module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.MulDiv
public import Proven.GKRProtocol.CleanArithmeticNative.MulDivCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.MulDiv
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 48. -/
theorem gate48 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate48.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate48.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨48, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate48 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[19]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨19, by decide⟩))

/-- The actual native sparse relation supplies gate 49. -/
theorem gate49 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate49.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate49.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨49, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate49 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[20]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨20, by decide⟩))

/-- The actual native sparse relation supplies gate 50. -/
theorem gate50 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate50.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate50.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨50, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate50 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[21]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨21, by decide⟩))

/-- The actual native sparse relation supplies gate 51. -/
theorem gate51 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate51.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate51.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨51, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate51 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[22]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨22, by decide⟩))

/-- The actual native sparse relation supplies gate 52. -/
theorem gate52 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate52.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate52.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gatesChecked _ (List.get_mem _ ⟨52, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate52 (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.MulDiv.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[23]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨23, by decide⟩))

/-- This batch retains every native scalar equation at these positions. -/
theorem gates003 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.MulDiv.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate48, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate49, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate50, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate51, Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate52], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0 :=
  (cons_holds (gate48 physical accepted) (cons_holds (gate49 physical accepted) (cons_holds (gate50 physical accepted) (cons_holds (gate51 physical accepted) (cons_holds (gate52 physical accepted) (by intro gate member; cases member))))))
end Airbender.Compiler.NativeBindings.MulDiv
