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

/-- The actual native sparse relation supplies gate 144. -/
theorem gate144 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate144.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate144.check = true :=
    all_at (index := 144) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate144) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[241]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry241 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate144 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry241).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate144, Expression.value, Function.comp_apply, coordinate142, coordinate203, coordinate204]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨241, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry241 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 145. -/
theorem gate145 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate145.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate145.check = true :=
    all_at (index := 145) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate145) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[242]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry242 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate145 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry242).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate145, Expression.value, Function.comp_apply, coordinate143, coordinate203, coordinate205]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨242, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry242 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 146. -/
theorem gate146 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate146.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate146.check = true :=
    all_at (index := 146) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate146) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[243]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry243 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate146 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry243).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate146, Expression.value, Function.comp_apply, coordinate144, coordinate203, coordinate206]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨243, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry243 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 147. -/
theorem gate147 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate147.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate147.check = true :=
    all_at (index := 147) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate147) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[244]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry244 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate147 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry244).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate147, Expression.value, Function.comp_apply, coordinate145, coordinate203, coordinate207]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨244, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry244 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 148. -/
theorem gate148 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate148.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate148.check = true :=
    all_at (index := 148) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate148) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[245]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry245 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate148 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry245).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate148, Expression.value, Function.comp_apply, coordinate146, coordinate203, coordinate208]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨245, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry245 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 149. -/
theorem gate149 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate149.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate149.check = true :=
    all_at (index := 149) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate149) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[246]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry246 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate149 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry246).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate149, Expression.value, Function.comp_apply, coordinate147, coordinate203, coordinate209]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨246, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry246 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 150. -/
theorem gate150 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate150.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate150.check = true :=
    all_at (index := 150) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate150) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[247]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry247 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate150 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry247).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate150, Expression.value, Function.comp_apply, coordinate148, coordinate203, coordinate210]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨247, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry247 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 151. -/
theorem gate151 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate151.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate151.check = true :=
    all_at (index := 151) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate151) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[248]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry248 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate151 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry248).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate151, Expression.value, Function.comp_apply, coordinate149, coordinate203, coordinate211]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨248, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry248 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 152. -/
theorem gate152 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate152.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate152.check = true :=
    all_at (index := 152) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate152) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[249]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry249 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate152 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry249).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate152, Expression.value, Function.comp_apply, coordinate150, coordinate203, coordinate212]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨249, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry249 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 153. -/
theorem gate153 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate153.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate153.check = true :=
    all_at (index := 153) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate153) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[250]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry250 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate153 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry250).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate153, Expression.value, Function.comp_apply, coordinate151, coordinate203, coordinate213]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨250, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry250 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 154. -/
theorem gate154 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate154.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate154.check = true :=
    all_at (index := 154) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate154) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[251]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry251 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate154 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry251).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate154, Expression.value, Function.comp_apply, coordinate142, coordinate202, coordinate214]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨251, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry251 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 155. -/
theorem gate155 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate155.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate155.check = true :=
    all_at (index := 155) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate155) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[252]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry252 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate155 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry252).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate155, Expression.value, Function.comp_apply, coordinate143, coordinate202, coordinate215]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨252, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry252 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 156. -/
theorem gate156 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate156.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate156.check = true :=
    all_at (index := 156) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate156) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[253]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry253 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate156 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry253).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate156, Expression.value, Function.comp_apply, coordinate144, coordinate202, coordinate216]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨253, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry253 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 157. -/
theorem gate157 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate157.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate157.check = true :=
    all_at (index := 157) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate157) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[254]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry254 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate157 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry254).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate157, Expression.value, Function.comp_apply, coordinate145, coordinate202, coordinate217]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨254, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry254 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 158. -/
theorem gate158 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate158.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate158.check = true :=
    all_at (index := 158) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate158) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[255]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry255 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate158 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry255).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate158, Expression.value, Function.comp_apply, coordinate146, coordinate202, coordinate218]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨255, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry255 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 159. -/
theorem gate159 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate159.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate159.check = true :=
    all_at (index := 159) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate159) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[256]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry256 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate159 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry256).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate159, Expression.value, Function.comp_apply, coordinate147, coordinate202, coordinate219]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨256, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry256 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- This batch retains every native scalar equation at these positions. -/
theorem gates009 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate144, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate145, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate146, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate147, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate148, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate149, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate150, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate151, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate152, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate153, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate154, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate155, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate156, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate157, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate158, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate159], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate144 physical accepted) (cons_holds (gate145 physical accepted) (cons_holds (gate146 physical accepted) (cons_holds (gate147 physical accepted) (cons_holds (gate148 physical accepted) (cons_holds (gate149 physical accepted) (cons_holds (gate150 physical accepted) (cons_holds (gate151 physical accepted) (cons_holds (gate152 physical accepted) (cons_holds (gate153 physical accepted) (cons_holds (gate154 physical accepted) (cons_holds (gate155 physical accepted) (cons_holds (gate156 physical accepted) (cons_holds (gate157 physical accepted) (cons_holds (gate158 physical accepted) (cons_holds (gate159 physical accepted) (by intro gate member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
