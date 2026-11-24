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

/-- The actual native sparse relation supplies gate 184. -/
theorem gate184 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate184.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate184.check = true :=
    all_at (index := 184) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate184) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[281]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry281 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate184 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry281).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate184, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression224, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression225, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression226, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression227, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression228, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression229, Expression.value, Function.comp_apply, coordinate5, coordinate9, coordinate13, coordinate17, coordinate25, coordinate29, coordinate33, coordinate103, coordinate105, coordinate107, coordinate109, coordinate113, coordinate115, coordinate117, coordinate121, coordinate123, coordinate125, coordinate129, coordinate133, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate214, coordinate218, coordinate221, coordinate222, coordinate223, coordinate244]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨281, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry281 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 185. -/
theorem gate185 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate185.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate185.check = true :=
    all_at (index := 185) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate185) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[282]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry282 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate185 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry282).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate185, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression235, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression236, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression237, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression238, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression239, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression240, Expression.value, Function.comp_apply, coordinate6, coordinate10, coordinate14, coordinate18, coordinate26, coordinate30, coordinate34, coordinate104, coordinate106, coordinate108, coordinate110, coordinate114, coordinate116, coordinate118, coordinate122, coordinate124, coordinate126, coordinate130, coordinate134, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate214, coordinate218, coordinate221, coordinate222, coordinate223, coordinate245]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨282, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry282 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)
end Airbender.Compiler.NativeBindings.BlakeRound
