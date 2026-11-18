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

/-- The actual native sparse relation supplies gate 190. -/
theorem gate190 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate190.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate190.check = true :=
    all_at (index := 190) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate190) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[287]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry287 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate190 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry287).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate190, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression288, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression289, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression290, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression291, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression292, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression293, Expression.value, Function.comp_apply, coordinate5, coordinate9, coordinate13, coordinate21, coordinate25, coordinate29, coordinate33, coordinate103, coordinate105, coordinate107, coordinate111, coordinate113, coordinate115, coordinate117, coordinate119, coordinate127, coordinate129, coordinate131, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate214, coordinate218, coordinate219, coordinate223, coordinate250]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨287, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry287 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 191. -/
theorem gate191 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate191.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate191.check = true :=
    all_at (index := 191) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate191) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[288]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry288 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate191 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry288).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate191, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression298, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression299, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression300, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression301, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression302, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression303, Expression.value, Function.comp_apply, coordinate6, coordinate10, coordinate14, coordinate22, coordinate26, coordinate30, coordinate34, coordinate104, coordinate106, coordinate108, coordinate112, coordinate114, coordinate116, coordinate118, coordinate120, coordinate128, coordinate130, coordinate132, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate214, coordinate218, coordinate219, coordinate223, coordinate251]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨288, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry288 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)
end Airbender.Compiler.NativeBindings.BlakeRound
