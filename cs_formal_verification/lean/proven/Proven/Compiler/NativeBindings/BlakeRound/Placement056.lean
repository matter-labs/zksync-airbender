module
public import Proven.Compiler.NativeBridge
public import Proven.Compiler.NativeBindings.BlakeRound.PlacementData
public import Proven.KernelRfl
public import Human.Compiler.Captures.BlakeRound
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.BlakeRound
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- Logical column 448 uses its actual native placement. -/
theorem placement448 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 448 = logical 448 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 448) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[448]'(by decide) = (448, (GKRAddress.BaseLayerWitness 309)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 448 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 309) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 309)) = (GKRAddress.BaseLayerWitness 309) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank448
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 449 uses its actual native placement. -/
theorem placement449 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 449 = logical 449 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 449) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[449]'(by decide) = (449, (GKRAddress.BaseLayerWitness 310)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 449 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 310) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 310)) = (GKRAddress.BaseLayerWitness 310) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank449
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 450 uses its actual native placement. -/
theorem placement450 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 450 = logical 450 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 450) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[450]'(by decide) = (450, (GKRAddress.BaseLayerWitness 311)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 450 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 311) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 311)) = (GKRAddress.BaseLayerWitness 311) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank450
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 451 uses its actual native placement. -/
theorem placement451 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 451 = logical 451 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 451) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[451]'(by decide) = (451, (GKRAddress.BaseLayerWitness 312)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 451 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 312) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 312)) = (GKRAddress.BaseLayerWitness 312) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank451
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 452 uses its actual native placement. -/
theorem placement452 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 452 = logical 452 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 452) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[452]'(by decide) = (452, (GKRAddress.BaseLayerWitness 313)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 452 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 313) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 313)) = (GKRAddress.BaseLayerWitness 313) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank452
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 453 uses its actual native placement. -/
theorem placement453 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 453 = logical 453 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 453) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[453]'(by decide) = (453, (GKRAddress.BaseLayerWitness 314)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 453 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 314) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 314)) = (GKRAddress.BaseLayerWitness 314) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank453
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 454 uses its actual native placement. -/
theorem placement454 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 454 = logical 454 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 454) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[454]'(by decide) = (454, (GKRAddress.BaseLayerWitness 315)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 454 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 315) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 315)) = (GKRAddress.BaseLayerWitness 315) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank454
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 455 uses its actual native placement. -/
theorem placement455 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 455 = logical 455 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 455) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[455]'(by decide) = (455, (GKRAddress.BaseLayerWitness 316)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 455 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 316) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 316)) = (GKRAddress.BaseLayerWitness 316) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank455
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Public placements cover each column in this batch. -/
theorem placements056 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    ∀ index ∈ [448, 449, 450, 451, 452, 453, 454, 455],
      (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement448 physical logical agreement) (cons_placements (placement449 physical logical agreement) (cons_placements (placement450 physical logical agreement) (cons_placements (placement451 physical logical agreement) (cons_placements (placement452 physical logical agreement) (cons_placements (placement453 physical logical agreement) (cons_placements (placement454 physical logical agreement) (cons_placements (placement455 physical logical agreement) (by intro index member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
