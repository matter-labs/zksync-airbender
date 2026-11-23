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

/-- The actual native sparse relation supplies gate 176. -/
theorem gate176 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate176.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate176.check = true :=
    all_at (index := 176) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate176) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[273]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry273 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate176 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry273).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate176, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression134, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression135, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression136, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression137, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression138, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression139, Expression.value, Function.comp_apply, coordinate5, coordinate9, coordinate13, coordinate17, coordinate21, coordinate25, coordinate29, coordinate33, coordinate103, coordinate105, coordinate107, coordinate109, coordinate111, coordinate113, coordinate115, coordinate117, coordinate119, coordinate123, coordinate125, coordinate129, coordinate133, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate215, coordinate216, coordinate217, coordinate218, coordinate219, coordinate236]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨273, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry273 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 177. -/
theorem gate177 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate177.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate177.check = true :=
    all_at (index := 177) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate177) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[274]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry274 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate177 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry274).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate177, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression145, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression146, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression147, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression148, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression149, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression150, Expression.value, Function.comp_apply, coordinate6, coordinate10, coordinate14, coordinate18, coordinate22, coordinate26, coordinate30, coordinate34, coordinate104, coordinate106, coordinate108, coordinate110, coordinate112, coordinate114, coordinate116, coordinate118, coordinate120, coordinate124, coordinate126, coordinate130, coordinate134, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate215, coordinate216, coordinate217, coordinate218, coordinate219, coordinate237]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨274, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry274 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)
end Airbender.Compiler.NativeBindings.BlakeRound
