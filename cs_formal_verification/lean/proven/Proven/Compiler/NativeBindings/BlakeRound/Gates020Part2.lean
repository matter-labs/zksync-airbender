module
public import Proven.Compiler.NativeLiteralBridge
public import Proven.Compiler.NativeBindings.BlakeRound.NativeData
public import Proven.Compiler.NativeBindings.BlakeRound.BankCoordinates
public import Proven.Compiler.NativeBindings.BlakeRound.CaptureData
public import Proven.KernelRfl
public import Human.Compiler.Captures.BlakeRound
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.BlakeRound
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 167. -/
theorem gate167 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate167.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate167.check = true :=
    all_at (index := 167) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate167) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[264]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry264 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate167 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry264).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate167, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression38, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression39, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression40, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression41, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression42, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression43, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression44, Expression.value, Function.comp_apply, coordinate6, coordinate10, coordinate14, coordinate18, coordinate22, coordinate26, coordinate34, coordinate104, coordinate106, coordinate108, coordinate110, coordinate112, coordinate114, coordinate118, coordinate120, coordinate122, coordinate124, coordinate126, coordinate128, coordinate134, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate215, coordinate216, coordinate217, coordinate219, coordinate221, coordinate222, coordinate227]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨264, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry264 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)
end Airbender.Compiler.NativeBindings.BlakeRound
