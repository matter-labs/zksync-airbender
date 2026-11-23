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

/-- The actual native sparse relation supplies gate 174. -/
theorem gate174 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate174.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate174.check = true :=
    all_at (index := 174) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate174) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[271]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry271 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate174 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry271).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate174, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression114, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression115, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression116, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression117, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression118, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression119, Expression.value, Function.comp_apply, coordinate9, coordinate13, coordinate17, coordinate21, coordinate25, coordinate29, coordinate33, coordinate105, coordinate107, coordinate109, coordinate111, coordinate113, coordinate115, coordinate117, coordinate125, coordinate127, coordinate129, coordinate133, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate215, coordinate217, coordinate219, coordinate220, coordinate234]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨271, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry271 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 175. -/
theorem gate175 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate175.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate175.check = true :=
    all_at (index := 175) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate175) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[272]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry272 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate175 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry272).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate175, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression124, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression125, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression126, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression127, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression128, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression129, Expression.value, Function.comp_apply, coordinate10, coordinate14, coordinate18, coordinate22, coordinate26, coordinate30, coordinate34, coordinate106, coordinate108, coordinate110, coordinate112, coordinate114, coordinate116, coordinate118, coordinate126, coordinate128, coordinate130, coordinate134, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate215, coordinate217, coordinate219, coordinate220, coordinate235]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨272, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry272 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)
end Airbender.Compiler.NativeBindings.BlakeRound
