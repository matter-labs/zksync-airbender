module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.SubwordMemory
public import Proven.GKRProtocol.CleanArithmeticNative.SubwordMemoryCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.SubwordMemory
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 48. -/
theorem gate48 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.SubwordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate48.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate48.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨48, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate48 (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[3]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨3, by decide⟩))

/-- The actual native sparse relation supplies gate 49. -/
theorem gate49 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.SubwordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate49.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate49.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨49, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate49 (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[4]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨4, by decide⟩))

/-- The actual native sparse relation supplies gate 50. -/
theorem gate50 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.SubwordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate50.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate50.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨50, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate50 (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[14]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨14, by decide⟩))

/-- The actual native sparse relation supplies gate 51. -/
theorem gate51 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.SubwordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate51.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate51.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨51, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate51 (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.SubwordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[15]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨15, by decide⟩))

/-- This batch retains every native scalar equation at these positions. -/
theorem gates003 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.SubwordMemory.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate48, Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate49, Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate50, Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate51], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address) = 0 :=
  (cons_holds (gate48 physical accepted) (cons_holds (gate49 physical accepted) (cons_holds (gate50 physical accepted) (cons_holds (gate51 physical accepted) (by intro gate member; cases member)))))
end Airbender.Compiler.NativeBindings.SubwordMemory
