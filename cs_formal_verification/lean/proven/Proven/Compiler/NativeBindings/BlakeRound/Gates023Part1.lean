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

/-- The actual native sparse relation supplies gate 186. -/
theorem gate186 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate186.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate186.check = true :=
    all_at (index := 186) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate186) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[283]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry283 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate186 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry283).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate186, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression246, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression247, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression248, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression249, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression250, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression251, Expression.value, Function.comp_apply, coordinate13, coordinate17, coordinate21, coordinate25, coordinate29, coordinate33, coordinate107, coordinate109, coordinate111, coordinate113, coordinate115, coordinate117, coordinate123, coordinate125, coordinate127, coordinate131, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate214, coordinate217, coordinate218, coordinate223, coordinate246]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨283, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry283 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 187. -/
theorem gate187 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate187.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate187.check = true :=
    all_at (index := 187) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate187) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[284]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry284 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate187 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry284).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate187, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression256, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression257, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression258, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression259, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression260, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression261, Expression.value, Function.comp_apply, coordinate14, coordinate18, coordinate22, coordinate26, coordinate30, coordinate34, coordinate108, coordinate110, coordinate112, coordinate114, coordinate116, coordinate118, coordinate124, coordinate126, coordinate128, coordinate132, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate214, coordinate217, coordinate218, coordinate223, coordinate247]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨284, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry284 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)
end Airbender.Compiler.NativeBindings.BlakeRound
