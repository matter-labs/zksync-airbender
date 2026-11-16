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

/-- The actual native sparse relation supplies gate 128. -/
theorem gate128 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate128.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate128.check = true :=
    all_at (index := 128) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate128) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[225]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry225 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate128 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry225).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate128, Expression.value, Function.comp_apply, coordinate73, coordinate142, coordinate188]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨225, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry225 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 129. -/
theorem gate129 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate129.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate129.check = true :=
    all_at (index := 129) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate129) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[226]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry226 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate129 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry226).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate129, Expression.value, Function.comp_apply, coordinate74, coordinate142, coordinate189]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨226, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry226 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 130. -/
theorem gate130 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate130.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate130.check = true :=
    all_at (index := 130) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate130) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[227]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry227 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate130 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry227).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate130, Expression.value, Function.comp_apply, coordinate77, coordinate142, coordinate190]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨227, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry227 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 131. -/
theorem gate131 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate131.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate131.check = true :=
    all_at (index := 131) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate131) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[228]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry228 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate131 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry228).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate131, Expression.value, Function.comp_apply, coordinate78, coordinate142, coordinate191]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨228, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry228 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 132. -/
theorem gate132 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate132.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate132.check = true :=
    all_at (index := 132) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate132) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[229]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry229 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate132 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry229).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate132, Expression.value, Function.comp_apply, coordinate81, coordinate142, coordinate192]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨229, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry229 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 133. -/
theorem gate133 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate133.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate133.check = true :=
    all_at (index := 133) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate133) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[230]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry230 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate133 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry230).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate133, Expression.value, Function.comp_apply, coordinate82, coordinate142, coordinate193]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨230, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry230 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 134. -/
theorem gate134 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate134.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate134.check = true :=
    all_at (index := 134) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate134) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[231]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry231 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate134 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry231).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate134, Expression.value, Function.comp_apply, coordinate89, coordinate142, coordinate194]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨231, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry231 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 135. -/
theorem gate135 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate135.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate135.check = true :=
    all_at (index := 135) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate135) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[232]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry232 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate135 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry232).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate135, Expression.value, Function.comp_apply, coordinate90, coordinate142, coordinate195]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨232, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry232 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 136. -/
theorem gate136 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate136.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate136.check = true :=
    all_at (index := 136) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate136) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[233]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry233 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate136 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry233).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate136, Expression.value, Function.comp_apply, coordinate97, coordinate142, coordinate196]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨233, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry233 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 137. -/
theorem gate137 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate137.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate137.check = true :=
    all_at (index := 137) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate137) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[234]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry234 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate137 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry234).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate137, Expression.value, Function.comp_apply, coordinate98, coordinate142, coordinate197]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨234, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry234 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 138. -/
theorem gate138 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate138.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate138.check = true :=
    all_at (index := 138) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate138) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[235]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry235 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate138 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry235).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate138, Expression.value, Function.comp_apply, coordinate85, coordinate141, coordinate142, coordinate153, coordinate198]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨235, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry235 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 139. -/
theorem gate139 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate139.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate139.check = true :=
    all_at (index := 139) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate139) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[236]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry236 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate139 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry236).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate139, Expression.value, Function.comp_apply, coordinate86, coordinate141, coordinate142, coordinate153, coordinate199]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨236, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry236 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 140. -/
theorem gate140 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate140.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate140.check = true :=
    all_at (index := 140) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate140) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[237]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry237 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate140 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry237).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate140, Expression.value, Function.comp_apply, coordinate93, coordinate141, coordinate142, coordinate153, coordinate200]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨237, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry237 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 141. -/
theorem gate141 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate141.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate141.check = true :=
    all_at (index := 141) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate141) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[238]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry238 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate141 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry238).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate141, Expression.value, Function.comp_apply, coordinate94, coordinate141, coordinate142, coordinate153, coordinate201]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨238, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry238 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 142. -/
theorem gate142 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate142.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate142.check = true :=
    all_at (index := 142) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate142) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[239]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry239 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate142 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry239).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate142, Expression.value, Function.comp_apply, coordinate140, coordinate141, coordinate202]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨239, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry239 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 143. -/
theorem gate143 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate143.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate143.check = true :=
    all_at (index := 143) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate143) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[240]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry240 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate143 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry240).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate143, Expression.value, Function.comp_apply, coordinate140, coordinate141, coordinate203]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨240, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry240 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- This batch retains every native scalar equation at these positions. -/
theorem gates008 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate128, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate129, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate130, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate131, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate132, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate133, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate134, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate135, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate136, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate137, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate138, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate139, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate140, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate141, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate142, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate143], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate128 physical accepted) (cons_holds (gate129 physical accepted) (cons_holds (gate130 physical accepted) (cons_holds (gate131 physical accepted) (cons_holds (gate132 physical accepted) (cons_holds (gate133 physical accepted) (cons_holds (gate134 physical accepted) (cons_holds (gate135 physical accepted) (cons_holds (gate136 physical accepted) (cons_holds (gate137 physical accepted) (cons_holds (gate138 physical accepted) (cons_holds (gate139 physical accepted) (cons_holds (gate140 physical accepted) (cons_holds (gate141 physical accepted) (cons_holds (gate142 physical accepted) (cons_holds (gate143 physical accepted) (by intro gate member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
