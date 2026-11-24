module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.Unified
public import Proven.GKRProtocol.CleanArithmeticNative.UnifiedCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.Unified
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 128. -/
theorem gate128 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate128.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate128.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨128, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate128 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[139]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨139, by decide⟩))

/-- The actual native sparse relation supplies gate 129. -/
theorem gate129 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate129.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate129.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gatesChecked _ (List.get_mem _ ⟨129, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate129 (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Unified.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Unified.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨0, by decide⟩))

/-- This batch retains every native scalar equation at these positions. -/
theorem gates008 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate128, Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.gate129], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 :=
  (cons_holds (gate128 physical accepted) (cons_holds (gate129 physical accepted) (by intro gate member; cases member)))
end Airbender.Compiler.NativeBindings.Unified
