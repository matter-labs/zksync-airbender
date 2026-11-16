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

/-- The actual native sparse relation supplies gate 208. -/
theorem gate208 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate208.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate208.check = true :=
    all_at (index := 208) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate208) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[305]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry305 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate208 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry305).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate208, Expression.value, Function.comp_apply, coordinate25, coordinate27, coordinate152, coordinate600, coordinate601]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨305, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry305 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 209. -/
theorem gate209 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate209.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate209.check = true :=
    all_at (index := 209) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate209) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[306]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry306 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate209 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry306).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate209, Expression.value, Function.comp_apply, coordinate26, coordinate28, coordinate152, coordinate606, coordinate607]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨306, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry306 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 210. -/
theorem gate210 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate210.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate210.check = true :=
    all_at (index := 210) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate210) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[307]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry307 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate210 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry307).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate210, Expression.value, Function.comp_apply, coordinate29, coordinate31, coordinate152, coordinate612, coordinate613]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨307, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry307 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 211. -/
theorem gate211 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate211.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate211.check = true :=
    all_at (index := 211) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate211) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[308]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry308 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate211 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry308).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate211, Expression.value, Function.comp_apply, coordinate30, coordinate32, coordinate152, coordinate618, coordinate619]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨308, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry308 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 212. -/
theorem gate212 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate212.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate212.check = true :=
    all_at (index := 212) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate212) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[309]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry309 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate212 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry309).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate212, Expression.value, Function.comp_apply, coordinate33, coordinate35, coordinate152, coordinate624, coordinate625]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨309, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry309 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 213. -/
theorem gate213 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate213.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate213.check = true :=
    all_at (index := 213) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate213) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[310]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry310 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate213 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry310).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate213, Expression.value, Function.comp_apply, coordinate34, coordinate36, coordinate152, coordinate630, coordinate631]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨310, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry310 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 214. -/
theorem gate214 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate214.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate214.check = true :=
    all_at (index := 214) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate214) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[311]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry311 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate214 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry311).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate214, Expression.value, Function.comp_apply, coordinate139]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨311, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry311 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 215. -/
theorem gate215 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate215.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate215.check = true :=
    all_at (index := 215) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate215) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[312]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry312 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate215 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry312).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate215, Expression.value, Function.comp_apply, coordinate140]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨312, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry312 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 216. -/
theorem gate216 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate216.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate216.check = true :=
    all_at (index := 216) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate216) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[313]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry313 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate216 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry313).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate216, Expression.value, Function.comp_apply, coordinate141]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨313, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry313 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 217. -/
theorem gate217 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate217.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate217.check = true :=
    all_at (index := 217) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate217) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[314]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry314 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate217 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry314).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate217, Expression.value, Function.comp_apply, coordinate142]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨314, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry314 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 218. -/
theorem gate218 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate218.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate218.check = true :=
    all_at (index := 218) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate218) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[315]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry315 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate218 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry315).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate218, Expression.value, Function.comp_apply, coordinate143]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨315, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry315 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 219. -/
theorem gate219 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate219.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate219.check = true :=
    all_at (index := 219) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate219) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[316]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry316 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate219 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry316).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate219, Expression.value, Function.comp_apply, coordinate144]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨316, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry316 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 220. -/
theorem gate220 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate220.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate220.check = true :=
    all_at (index := 220) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate220) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[317]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry317 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate220 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry317).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate220, Expression.value, Function.comp_apply, coordinate145]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨317, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry317 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 221. -/
theorem gate221 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate221.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate221.check = true :=
    all_at (index := 221) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate221) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[318]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry318 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate221 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry318).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate221, Expression.value, Function.comp_apply, coordinate146]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨318, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry318 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 222. -/
theorem gate222 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate222.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate222.check = true :=
    all_at (index := 222) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate222) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[319]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry319 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate222 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry319).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate222, Expression.value, Function.comp_apply, coordinate147]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨319, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry319 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 223. -/
theorem gate223 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate223.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate223.check = true :=
    all_at (index := 223) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate223) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[320]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry320 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate223 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry320).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate223, Expression.value, Function.comp_apply, coordinate148]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨320, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry320 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- This batch retains every native scalar equation at these positions. -/
theorem gates013 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate208, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate209, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate210, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate211, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate212, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate213, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate214, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate215, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate216, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate217, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate218, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate219, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate220, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate221, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate222, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate223], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate208 physical accepted) (cons_holds (gate209 physical accepted) (cons_holds (gate210 physical accepted) (cons_holds (gate211 physical accepted) (cons_holds (gate212 physical accepted) (cons_holds (gate213 physical accepted) (cons_holds (gate214 physical accepted) (cons_holds (gate215 physical accepted) (cons_holds (gate216 physical accepted) (cons_holds (gate217 physical accepted) (cons_holds (gate218 physical accepted) (cons_holds (gate219 physical accepted) (cons_holds (gate220 physical accepted) (cons_holds (gate221 physical accepted) (cons_holds (gate222 physical accepted) (cons_holds (gate223 physical accepted) (by intro gate member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
