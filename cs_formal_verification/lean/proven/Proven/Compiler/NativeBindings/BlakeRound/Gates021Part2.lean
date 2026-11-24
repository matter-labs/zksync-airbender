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

/-- The actual native sparse relation supplies gate 172. -/
theorem gate172 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate172.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate172.check = true :=
    all_at (index := 172) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate172) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[269]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry269 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate172 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry269).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate172, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression92, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression93, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression94, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression95, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression96, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression97, Expression.value, Function.comp_apply, coordinate5, coordinate9, coordinate13, coordinate17, coordinate21, coordinate25, coordinate29, coordinate33, coordinate103, coordinate105, coordinate107, coordinate109, coordinate111, coordinate113, coordinate115, coordinate117, coordinate121, coordinate125, coordinate127, coordinate129, coordinate131, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate215, coordinate217, coordinate220, coordinate221, coordinate222, coordinate232]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨269, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry269 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 173. -/
theorem gate173 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate173.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate173.check = true :=
    all_at (index := 173) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate173) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[270]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry270 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate173 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry270).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate173, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression103, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression104, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression105, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression106, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression107, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression108, Expression.value, Function.comp_apply, coordinate6, coordinate10, coordinate14, coordinate18, coordinate22, coordinate26, coordinate30, coordinate34, coordinate104, coordinate106, coordinate108, coordinate110, coordinate112, coordinate114, coordinate116, coordinate118, coordinate122, coordinate126, coordinate128, coordinate130, coordinate132, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate215, coordinate217, coordinate220, coordinate221, coordinate222, coordinate233]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨270, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry270 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)
end Airbender.Compiler.NativeBindings.BlakeRound
