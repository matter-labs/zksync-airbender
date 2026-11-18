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

/-- The actual native sparse relation supplies gate 165. -/
theorem gate165 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate165.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate165.check = true :=
    all_at (index := 165) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate165) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[262]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry262 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate165 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry262).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate165, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression14, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression15, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression16, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression17, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression18, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression19, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression20, Expression.value, Function.comp_apply, coordinate6, coordinate10, coordinate14, coordinate18, coordinate22, coordinate26, coordinate30, coordinate34, coordinate104, coordinate106, coordinate108, coordinate110, coordinate112, coordinate114, coordinate116, coordinate118, coordinate122, coordinate124, coordinate126, coordinate128, coordinate130, coordinate132, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate215, coordinate216, coordinate218, coordinate220, coordinate221, coordinate223, coordinate225]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨262, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry262 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 166. -/
theorem gate166 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate166.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate166.check = true :=
    all_at (index := 166) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate166) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[263]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry263 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate166 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry263).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate166, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression26, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression27, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression28, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression29, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression30, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression31, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression32, Expression.value, Function.comp_apply, coordinate5, coordinate9, coordinate13, coordinate17, coordinate21, coordinate25, coordinate33, coordinate103, coordinate105, coordinate107, coordinate109, coordinate111, coordinate113, coordinate117, coordinate119, coordinate121, coordinate123, coordinate125, coordinate127, coordinate133, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate215, coordinate216, coordinate217, coordinate219, coordinate221, coordinate222, coordinate226]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨263, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry263 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)
end Airbender.Compiler.NativeBindings.BlakeRound
