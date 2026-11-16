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

/-- The actual native sparse relation supplies gate 112. -/
theorem gate112 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate112.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate112.check = true :=
    all_at (index := 112) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate112) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[209]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry209 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate112 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry209).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate112, Expression.value, Function.comp_apply, coordinate22, coordinate141, coordinate172]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨209, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry209 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 113. -/
theorem gate113 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate113.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate113.check = true :=
    all_at (index := 113) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate113) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[210]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry210 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate113 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry210).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate113, Expression.value, Function.comp_apply, coordinate54, coordinate142, coordinate172, coordinate173]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨210, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry210 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 114. -/
theorem gate114 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate114.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate114.check = true :=
    all_at (index := 114) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate114) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[211]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry211 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate114 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry211).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate114, Expression.value, Function.comp_apply, coordinate25, coordinate141, coordinate174]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨211, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry211 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 115. -/
theorem gate115 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate115.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate115.check = true :=
    all_at (index := 115) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate115) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[212]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry212 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate115 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry212).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate115, Expression.value, Function.comp_apply, coordinate57, coordinate142, coordinate174, coordinate175]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨212, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry212 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 116. -/
theorem gate116 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate116.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate116.check = true :=
    all_at (index := 116) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate116) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[213]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry213 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate116 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry213).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate116, Expression.value, Function.comp_apply, coordinate26, coordinate141, coordinate176]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨213, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry213 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 117. -/
theorem gate117 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate117.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate117.check = true :=
    all_at (index := 117) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate117) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[214]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry214 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate117 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry214).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate117, Expression.value, Function.comp_apply, coordinate58, coordinate142, coordinate176, coordinate177]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨214, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry214 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 118. -/
theorem gate118 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate118.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate118.check = true :=
    all_at (index := 118) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate118) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[215]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry215 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate118 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry215).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate118, Expression.value, Function.comp_apply, coordinate29, coordinate141, coordinate178]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨215, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry215 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 119. -/
theorem gate119 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate119.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate119.check = true :=
    all_at (index := 119) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate119) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[216]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry216 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate119 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry216).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate119, Expression.value, Function.comp_apply, coordinate61, coordinate142, coordinate178, coordinate179]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨216, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry216 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 120. -/
theorem gate120 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate120.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate120.check = true :=
    all_at (index := 120) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate120) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[217]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry217 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate120 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry217).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate120, Expression.value, Function.comp_apply, coordinate30, coordinate141, coordinate180]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨217, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry217 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 121. -/
theorem gate121 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate121.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate121.check = true :=
    all_at (index := 121) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate121) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[218]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry218 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate121 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry218).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate121, Expression.value, Function.comp_apply, coordinate62, coordinate142, coordinate180, coordinate181]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨218, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry218 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 122. -/
theorem gate122 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate122.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate122.check = true :=
    all_at (index := 122) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate122) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[219]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry219 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate122 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry219).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate122, Expression.value, Function.comp_apply, coordinate33, coordinate141, coordinate182]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨219, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry219 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 123. -/
theorem gate123 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate123.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate123.check = true :=
    all_at (index := 123) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate123) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[220]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry220 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate123 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry220).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate123, Expression.value, Function.comp_apply, coordinate65, coordinate142, coordinate182, coordinate183]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨220, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry220 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 124. -/
theorem gate124 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate124.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate124.check = true :=
    all_at (index := 124) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate124) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[221]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry221 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate124 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry221).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate124, Expression.value, Function.comp_apply, coordinate34, coordinate141, coordinate184]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨221, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry221 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 125. -/
theorem gate125 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate125.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate125.check = true :=
    all_at (index := 125) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate125) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[222]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry222 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate125 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry222).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate125, Expression.value, Function.comp_apply, coordinate66, coordinate142, coordinate184, coordinate185]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨222, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry222 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 126. -/
theorem gate126 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate126.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate126.check = true :=
    all_at (index := 126) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate126) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[223]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry223 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate126 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry223).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate126, Expression.value, Function.comp_apply, coordinate69, coordinate142, coordinate186]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨223, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry223 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 127. -/
theorem gate127 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate127.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate127.check = true :=
    all_at (index := 127) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate127) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[224]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry224 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate127 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry224).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate127, Expression.value, Function.comp_apply, coordinate70, coordinate142, coordinate187]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨224, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry224 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- This batch retains every native scalar equation at these positions. -/
theorem gates007 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate112, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate113, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate114, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate115, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate116, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate117, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate118, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate119, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate120, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate121, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate122, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate123, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate124, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate125, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate126, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate127], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate112 physical accepted) (cons_holds (gate113 physical accepted) (cons_holds (gate114 physical accepted) (cons_holds (gate115 physical accepted) (cons_holds (gate116 physical accepted) (cons_holds (gate117 physical accepted) (cons_holds (gate118 physical accepted) (cons_holds (gate119 physical accepted) (cons_holds (gate120 physical accepted) (cons_holds (gate121 physical accepted) (cons_holds (gate122 physical accepted) (cons_holds (gate123 physical accepted) (cons_holds (gate124 physical accepted) (cons_holds (gate125 physical accepted) (cons_holds (gate126 physical accepted) (cons_holds (gate127 physical accepted) (by intro gate member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
