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

/-- The actual native sparse relation supplies gate 200. -/
theorem gate200 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate200.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate200.check = true :=
    all_at (index := 200) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate200) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[297]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry297 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate200 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry297).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate200, Expression.value, Function.comp_apply, coordinate9, coordinate11, coordinate152, coordinate552, coordinate553]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨297, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry297 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 201. -/
theorem gate201 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate201.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate201.check = true :=
    all_at (index := 201) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate201) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[298]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry298 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate201 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry298).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate201, Expression.value, Function.comp_apply, coordinate10, coordinate12, coordinate152, coordinate558, coordinate559]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨298, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry298 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 202. -/
theorem gate202 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate202.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate202.check = true :=
    all_at (index := 202) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate202) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[299]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry299 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate202 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry299).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate202, Expression.value, Function.comp_apply, coordinate13, coordinate15, coordinate152, coordinate564, coordinate565]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨299, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry299 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 203. -/
theorem gate203 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate203.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate203.check = true :=
    all_at (index := 203) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate203) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[300]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry300 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate203 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry300).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate203, Expression.value, Function.comp_apply, coordinate14, coordinate16, coordinate152, coordinate570, coordinate571]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨300, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry300 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 204. -/
theorem gate204 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate204.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate204.check = true :=
    all_at (index := 204) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate204) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[301]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry301 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate204 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry301).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate204, Expression.value, Function.comp_apply, coordinate17, coordinate19, coordinate152, coordinate576, coordinate577]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨301, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry301 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 205. -/
theorem gate205 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate205.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate205.check = true :=
    all_at (index := 205) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate205) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[302]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry302 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate205 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry302).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate205, Expression.value, Function.comp_apply, coordinate18, coordinate20, coordinate152, coordinate582, coordinate583]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨302, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry302 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 206. -/
theorem gate206 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate206.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate206.check = true :=
    all_at (index := 206) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate206) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[303]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry303 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate206 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry303).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate206, Expression.value, Function.comp_apply, coordinate21, coordinate23, coordinate152, coordinate588, coordinate589]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨303, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry303 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 207. -/
theorem gate207 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate207.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate207.check = true :=
    all_at (index := 207) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate207) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[304]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry304 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate207 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry304).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate207, Expression.value, Function.comp_apply, coordinate22, coordinate24, coordinate152, coordinate594, coordinate595]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨304, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry304 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- This batch retains every native scalar equation at these positions. -/
theorem gates025 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate200, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate201, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate202, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate203, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate204, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate205, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate206, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate207], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate200 physical accepted) (cons_holds (gate201 physical accepted) (cons_holds (gate202 physical accepted) (cons_holds (gate203 physical accepted) (cons_holds (gate204 physical accepted) (cons_holds (gate205 physical accepted) (cons_holds (gate206 physical accepted) (cons_holds (gate207 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
