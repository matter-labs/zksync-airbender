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

/-- The actual native sparse relation supplies gate 188. -/
theorem gate188 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate188.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate188.check = true :=
    all_at (index := 188) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate188) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[285]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry285 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate188 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry285).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate188, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression266, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression267, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression268, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression269, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression270, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression271, Expression.value, Function.comp_apply, coordinate5, coordinate9, coordinate17, coordinate21, coordinate29, coordinate33, coordinate103, coordinate105, coordinate109, coordinate111, coordinate115, coordinate117, coordinate119, coordinate121, coordinate125, coordinate127, coordinate133, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate214, coordinate215, coordinate219, coordinate220, coordinate221, coordinate248]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨285, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry285 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 189. -/
theorem gate189 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate189.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate189.check = true :=
    all_at (index := 189) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate189) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[286]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry286 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate189 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry286).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate189, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression277, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression278, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression279, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression280, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression281, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression282, Expression.value, Function.comp_apply, coordinate6, coordinate10, coordinate18, coordinate22, coordinate30, coordinate34, coordinate104, coordinate106, coordinate110, coordinate112, coordinate116, coordinate118, coordinate120, coordinate122, coordinate126, coordinate128, coordinate134, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate214, coordinate215, coordinate219, coordinate220, coordinate221, coordinate249]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨286, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry286 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)
end Airbender.Compiler.NativeBindings.BlakeRound
