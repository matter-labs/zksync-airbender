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

/-- The actual native sparse relation supplies gate 168. -/
theorem gate168 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate168.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate168.check = true :=
    all_at (index := 168) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate168) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[265]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry265 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate168 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry265).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate168, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression50, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression51, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression52, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression53, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression54, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression55, Expression.value, Function.comp_apply, coordinate5, coordinate9, coordinate13, coordinate17, coordinate21, coordinate25, coordinate29, coordinate33, coordinate103, coordinate105, coordinate107, coordinate109, coordinate111, coordinate113, coordinate115, coordinate117, coordinate119, coordinate127, coordinate131, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate216, coordinate222, coordinate223, coordinate228]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨265, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry265 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 169. -/
theorem gate169 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate169.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate169.check = true :=
    all_at (index := 169) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate169) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[266]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry266 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate169 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry266).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate169, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression60, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression61, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression62, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression63, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression64, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.sharedExpression65, Expression.value, Function.comp_apply, coordinate6, coordinate10, coordinate14, coordinate18, coordinate22, coordinate26, coordinate30, coordinate34, coordinate104, coordinate106, coordinate108, coordinate110, coordinate112, coordinate114, coordinate116, coordinate118, coordinate120, coordinate128, coordinate132, coordinate142, coordinate143, coordinate144, coordinate145, coordinate146, coordinate147, coordinate148, coordinate149, coordinate150, coordinate151, coordinate204, coordinate205, coordinate206, coordinate207, coordinate208, coordinate209, coordinate210, coordinate211, coordinate212, coordinate213, coordinate216, coordinate222, coordinate223, coordinate229]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨266, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry266 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

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

/-- This batch retains every native scalar equation at these positions. -/
theorem gates021 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate168, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate169, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate170, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate171, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate172, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate173, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate174, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate175], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate168 physical accepted) (cons_holds (gate169 physical accepted) (cons_holds (gate170 physical accepted) (cons_holds (gate171 physical accepted) (cons_holds (gate172 physical accepted) (cons_holds (gate173 physical accepted) (cons_holds (gate174 physical accepted) (cons_holds (gate175 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
