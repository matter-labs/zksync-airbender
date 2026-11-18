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
theorem gates015 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate120, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate121, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate122, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate123, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate124, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate125, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate126, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate127], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate120 physical accepted) (cons_holds (gate121 physical accepted) (cons_holds (gate122 physical accepted) (cons_holds (gate123 physical accepted) (cons_holds (gate124 physical accepted) (cons_holds (gate125 physical accepted) (cons_holds (gate126 physical accepted) (cons_holds (gate127 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
