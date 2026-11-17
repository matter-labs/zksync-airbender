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

/-- The actual native sparse relation supplies gate 192. -/
theorem gate192 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate192.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate192.check = true :=
    all_at (index := 192) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate192) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[289]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry289 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate192 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry289).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate192, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression308, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression309, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression310, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression311, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression312, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression313, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression314, Expression.value, Function.comp_apply, coordinate5, coordinate9, coordinate13, coordinate17, coordinate25, coordinate29, coordinate33, coordinate103, coordinate105, coordinate107, coordinate109, coordinate113, coordinate115, coordinate117, coordinate119, coordinate121, coordinate123, coordinate129, coordinate131, coordinate133, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate214, coordinate216, coordinate217, coordinate220, coordinate222, coordinate223, coordinate252]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨289, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry289 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 193. -/
theorem gate193 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate193.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate193.check = true :=
    all_at (index := 193) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate193) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[290]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry290 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate193 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry290).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate193, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression320, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression321, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression322, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression323, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression324, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression325, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression326, Expression.value, Function.comp_apply, coordinate6, coordinate10, coordinate14, coordinate18, coordinate26, coordinate30, coordinate34, coordinate104, coordinate106, coordinate108, coordinate110, coordinate114, coordinate116, coordinate118, coordinate120, coordinate122, coordinate124, coordinate130, coordinate132, coordinate134, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate214, coordinate216, coordinate217, coordinate220, coordinate222, coordinate223, coordinate253]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨290, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry290 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)
end Airbender.Compiler.NativeBindings.BlakeRound
