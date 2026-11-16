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

/-- The actual native sparse relation supplies gate 176. -/
theorem gate176 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate176.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate176.check = true :=
    all_at (index := 176) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate176) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[273]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry273 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate176 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry273).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate176, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression134, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression135, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression136, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression137, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression138, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression139, Expression.value, Function.comp_apply, coordinate5, coordinate9, coordinate13, coordinate17, coordinate21, coordinate25, coordinate29, coordinate33, coordinate103, coordinate105, coordinate107, coordinate109, coordinate111, coordinate113, coordinate115, coordinate117, coordinate119, coordinate123, coordinate125, coordinate129, coordinate133, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate215, coordinate216, coordinate217, coordinate218, coordinate219, coordinate236]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨273, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry273 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 177. -/
theorem gate177 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate177.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate177.check = true :=
    all_at (index := 177) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate177) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[274]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry274 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate177 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry274).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate177, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression145, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression146, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression147, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression148, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression149, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression150, Expression.value, Function.comp_apply, coordinate6, coordinate10, coordinate14, coordinate18, coordinate22, coordinate26, coordinate30, coordinate34, coordinate104, coordinate106, coordinate108, coordinate110, coordinate112, coordinate114, coordinate116, coordinate118, coordinate120, coordinate124, coordinate126, coordinate130, coordinate134, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate215, coordinate216, coordinate217, coordinate218, coordinate219, coordinate237]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨274, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry274 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 178. -/
theorem gate178 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate178.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate178.check = true :=
    all_at (index := 178) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate178) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[275]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry275 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate178 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry275).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate178, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression156, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression157, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression158, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression159, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression160, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression161, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression162, Expression.value, Function.comp_apply, coordinate5, coordinate9, coordinate13, coordinate17, coordinate25, coordinate29, coordinate33, coordinate103, coordinate105, coordinate107, coordinate109, coordinate113, coordinate115, coordinate117, coordinate119, coordinate121, coordinate123, coordinate129, coordinate131, coordinate133, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate216, coordinate217, coordinate218, coordinate220, coordinate221, coordinate222, coordinate238]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨275, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry275 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 179. -/
theorem gate179 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate179.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate179.check = true :=
    all_at (index := 179) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate179) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[276]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry276 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate179 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry276).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate179, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression168, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression169, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression170, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression171, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression172, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression173, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression174, Expression.value, Function.comp_apply, coordinate6, coordinate10, coordinate14, coordinate18, coordinate26, coordinate30, coordinate34, coordinate104, coordinate106, coordinate108, coordinate110, coordinate114, coordinate116, coordinate118, coordinate120, coordinate122, coordinate124, coordinate130, coordinate132, coordinate134, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate216, coordinate217, coordinate218, coordinate220, coordinate221, coordinate222, coordinate239]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨276, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry276 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

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

/-- The actual native sparse relation supplies gate 182. -/
theorem gate182 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate182.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate182.check = true :=
    all_at (index := 182) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate182) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[279]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry279 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate182 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry279).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate182, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression202, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression203, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression204, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression205, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression206, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression207, Expression.value, Function.comp_apply, coordinate5, coordinate9, coordinate13, coordinate17, coordinate21, coordinate25, coordinate29, coordinate33, coordinate103, coordinate105, coordinate107, coordinate109, coordinate111, coordinate113, coordinate115, coordinate117, coordinate121, coordinate125, coordinate127, coordinate129, coordinate131, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate214, coordinate215, coordinate216, coordinate219, coordinate223, coordinate242]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨279, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry279 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 183. -/
theorem gate183 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate183.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate183.check = true :=
    all_at (index := 183) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate183) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[280]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry280 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate183 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry280).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate183, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression213, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression214, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression215, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression216, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression217, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression218, Expression.value, Function.comp_apply, coordinate6, coordinate10, coordinate14, coordinate18, coordinate22, coordinate26, coordinate30, coordinate34, coordinate104, coordinate106, coordinate108, coordinate110, coordinate112, coordinate114, coordinate116, coordinate118, coordinate122, coordinate126, coordinate128, coordinate130, coordinate132, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate214, coordinate215, coordinate216, coordinate219, coordinate223, coordinate243]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨280, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry280 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- This batch retains every native scalar equation at these positions. -/
theorem gates022 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate176, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate177, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate178, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate179, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate180, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate181, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate182, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate183], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate176 physical accepted) (cons_holds (gate177 physical accepted) (cons_holds (gate178 physical accepted) (cons_holds (gate179 physical accepted) (cons_holds (gate180 physical accepted) (cons_holds (gate181 physical accepted) (cons_holds (gate182 physical accepted) (cons_holds (gate183 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
