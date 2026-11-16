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

/-- This batch retains every native scalar equation at these positions. -/
theorem gates023 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate184, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate185, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate186, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate187, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate188, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate189, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate190, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate191], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate184 physical accepted) (cons_holds (gate185 physical accepted) (cons_holds (gate186 physical accepted) (cons_holds (gate187 physical accepted) (cons_holds (gate188 physical accepted) (cons_holds (gate189 physical accepted) (cons_holds (gate190 physical accepted) (cons_holds (gate191 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
