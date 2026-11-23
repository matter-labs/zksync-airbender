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

/-- The actual native sparse relation supplies gate 170. -/
theorem gate170 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate170.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate170.check = true :=
    all_at (index := 170) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate170) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[267]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry267 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate170 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry267).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate170, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression70, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression71, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression72, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression73, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression74, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression75, Expression.value, Function.comp_apply, coordinate5, coordinate9, coordinate13, coordinate17, coordinate21, coordinate29, coordinate33, coordinate103, coordinate105, coordinate107, coordinate109, coordinate111, coordinate115, coordinate117, coordinate119, coordinate121, coordinate123, coordinate131, coordinate133, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate215, coordinate219, coordinate220, coordinate221, coordinate222, coordinate230]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨267, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry267 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 171. -/
theorem gate171 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate171.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate171.check = true :=
    all_at (index := 171) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate171) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[268]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry268 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate171 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry268).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate171, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression81, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression82, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression83, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression84, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression85, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression86, Expression.value, Function.comp_apply, coordinate6, coordinate10, coordinate14, coordinate18, coordinate22, coordinate30, coordinate34, coordinate104, coordinate106, coordinate108, coordinate110, coordinate112, coordinate116, coordinate118, coordinate120, coordinate122, coordinate124, coordinate132, coordinate134, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate215, coordinate219, coordinate220, coordinate221, coordinate222, coordinate231]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨268, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry268 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)
end Airbender.Compiler.NativeBindings.BlakeRound
