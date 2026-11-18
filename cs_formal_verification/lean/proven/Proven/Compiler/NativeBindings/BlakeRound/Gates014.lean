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

/-- This batch retains every native scalar equation at these positions. -/
theorem gates014 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate112, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate113, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate114, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate115, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate116, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate117, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate118, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate119], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate112 physical accepted) (cons_holds (gate113 physical accepted) (cons_holds (gate114 physical accepted) (cons_holds (gate115 physical accepted) (cons_holds (gate116 physical accepted) (cons_holds (gate117 physical accepted) (cons_holds (gate118 physical accepted) (cons_holds (gate119 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
