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

/-- The actual native sparse relation supplies gate 180. -/
theorem gate180 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate180.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate180.check = true :=
    all_at (index := 180) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate180) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[277]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry277 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate180 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry277).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate180, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression180, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression181, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression182, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression183, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression184, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression185, Expression.value, Function.comp_apply, coordinate5, coordinate9, coordinate13, coordinate21, coordinate25, coordinate29, coordinate33, coordinate103, coordinate105, coordinate107, coordinate111, coordinate113, coordinate115, coordinate117, coordinate119, coordinate123, coordinate127, coordinate131, coordinate133, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate214, coordinate216, coordinate218, coordinate222, coordinate223, coordinate240]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨277, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry277 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 181. -/
theorem gate181 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate181.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate181.check = true :=
    all_at (index := 181) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate181) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[278]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry278 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate181 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry278).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate181, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression191, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression192, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression193, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression194, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression195, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression196, Expression.value, Function.comp_apply, coordinate6, coordinate10, coordinate14, coordinate22, coordinate26, coordinate30, coordinate34, coordinate104, coordinate106, coordinate108, coordinate112, coordinate114, coordinate116, coordinate118, coordinate120, coordinate124, coordinate128, coordinate132, coordinate134, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate214, coordinate216, coordinate218, coordinate222, coordinate223, coordinate241]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨278, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry278 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)
end Airbender.Compiler.NativeBindings.BlakeRound
