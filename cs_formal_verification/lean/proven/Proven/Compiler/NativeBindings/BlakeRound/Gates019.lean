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

/-- The actual native sparse relation supplies gate 304. -/
theorem gate304 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate304.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate304.check = true :=
    all_at (index := 304) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate304) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[401]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry401 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate304 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry401).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate304, Expression.value, Function.comp_apply, coordinate669]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨401, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry401 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 305. -/
theorem gate305 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate305.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate305.check = true :=
    all_at (index := 305) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate305) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[402]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry402 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate305 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry402).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate305, Expression.value, Function.comp_apply, coordinate670]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨402, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry402 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 306. -/
theorem gate306 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate306.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate306.check = true :=
    all_at (index := 306) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate306) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[403]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry403 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate306 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry403).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate306, Expression.value, Function.comp_apply, coordinate671]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨403, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry403 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 307. -/
theorem gate307 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate307.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate307.check = true :=
    all_at (index := 307) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate307) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[404]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry404 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate307 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry404).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate307, Expression.value, Function.comp_apply, coordinate672]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨404, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry404 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 308. -/
theorem gate308 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate308.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate308.check = true :=
    all_at (index := 308) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate308) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[405]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry405 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate308 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry405).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate308, Expression.value, Function.comp_apply, coordinate673]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨405, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry405 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 309. -/
theorem gate309 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate309.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate309.check = true :=
    all_at (index := 309) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate309) scalar_gate_data_checked (by cbv)
  have captured : (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[406]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry406 :=
    entry_of_binding (by decide) layer0_gates (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate309 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate (Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry406).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate309, Expression.value, Function.comp_apply, coordinate674]
    rfl
  have acceptedEntry := gate_at_literal accepted ⟨0, by decide⟩ ⟨406, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0GatesEntry406 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 310. -/
theorem gate310 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate310.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate310.check = true :=
    all_at (index := 310) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate310) scalar_gate_data_checked (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate310 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate310, Function.comp_apply, coordinate763, coordinate764]
    rfl
  have acceptedEntry := gate_at accepted ⟨1, by decide⟩ ⟨0, by decide⟩
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 311. -/
theorem gate311 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate311.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate311.check = true :=
    all_at (index := 311) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate311) scalar_gate_data_checked (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate311 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[2]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[2]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate311, Function.comp_apply, coordinate764, coordinate765]
    rfl
  have acceptedEntry := gate_at accepted ⟨2, by decide⟩ ⟨0, by decide⟩
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 312. -/
theorem gate312 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate312.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate312.check = true :=
    all_at (index := 312) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate312) scalar_gate_data_checked (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate312 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[3]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[3]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate312, Function.comp_apply, coordinate765, coordinate766]
    rfl
  have acceptedEntry := gate_at accepted ⟨3, by decide⟩ ⟨0, by decide⟩
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 313. -/
theorem gate313 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate313.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate313.check = true :=
    all_at (index := 313) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate313) scalar_gate_data_checked (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate313 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[4]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[4]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate313, Function.comp_apply, coordinate766, coordinate767]
    rfl
  have acceptedEntry := gate_at accepted ⟨4, by decide⟩ ⟨0, by decide⟩
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 314. -/
theorem gate314 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate314.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate314.check = true :=
    all_at (index := 314) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate314) scalar_gate_data_checked (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate314 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[5]'(by decide)).gates ++ ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[5]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate314, Function.comp_apply, coordinate767, coordinate768]
    rfl
  have acceptedEntry := gate_at accepted ⟨5, by decide⟩ ⟨0, by decide⟩
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- This batch retains every native scalar equation at these positions. -/
theorem gates019 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate304, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate305, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate306, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate307, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate308, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate309, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate310, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate311, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate312, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate313, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate314], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate304 physical accepted) (cons_holds (gate305 physical accepted) (cons_holds (gate306 physical accepted) (cons_holds (gate307 physical accepted) (cons_holds (gate308 physical accepted) (cons_holds (gate309 physical accepted) (cons_holds (gate310 physical accepted) (cons_holds (gate311 physical accepted) (cons_holds (gate312 physical accepted) (cons_holds (gate313 physical accepted) (cons_holds (gate314 physical accepted) (by intro gate member; cases member))))))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
