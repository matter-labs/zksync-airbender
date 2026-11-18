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

/-- Logical column 520 uses its actual native placement. -/
theorem placement520 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 520 = logical 520 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 520) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[520]'(by decide) = (520, (GKRAddress.BaseLayerWitness 381)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 520 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 381) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 381)) = (GKRAddress.BaseLayerWitness 381) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank520
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 521 uses its actual native placement. -/
theorem placement521 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 521 = logical 521 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 521) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[521]'(by decide) = (521, (GKRAddress.BaseLayerWitness 382)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 521 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 382) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 382)) = (GKRAddress.BaseLayerWitness 382) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank521
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 522 uses its actual native placement. -/
theorem placement522 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 522 = logical 522 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 522) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[522]'(by decide) = (522, (GKRAddress.BaseLayerWitness 383)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 522 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 383) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 383)) = (GKRAddress.BaseLayerWitness 383) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank522
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 523 uses its actual native placement. -/
theorem placement523 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 523 = logical 523 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 523) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[523]'(by decide) = (523, (GKRAddress.BaseLayerWitness 384)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 523 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 384) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 384)) = (GKRAddress.BaseLayerWitness 384) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank523
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 524 uses its actual native placement. -/
theorem placement524 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 524 = logical 524 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 524) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[524]'(by decide) = (524, (GKRAddress.BaseLayerWitness 385)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 524 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 385) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 385)) = (GKRAddress.BaseLayerWitness 385) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank524
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 525 uses its actual native placement. -/
theorem placement525 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 525 = logical 525 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 525) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[525]'(by decide) = (525, (GKRAddress.BaseLayerWitness 386)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 525 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 386) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 386)) = (GKRAddress.BaseLayerWitness 386) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank525
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 526 uses its actual native placement. -/
theorem placement526 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 526 = logical 526 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 526) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[526]'(by decide) = (526, (GKRAddress.BaseLayerWitness 387)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 526 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 387) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 387)) = (GKRAddress.BaseLayerWitness 387) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank526
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 527 uses its actual native placement. -/
theorem placement527 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 527 = logical 527 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 527) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[527]'(by decide) = (527, (GKRAddress.BaseLayerWitness 388)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 527 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 388) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 388)) = (GKRAddress.BaseLayerWitness 388) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank527
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Public placements cover each column in this batch. -/
theorem placements065 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    ∀ index ∈ [520, 521, 522, 523, 524, 525, 526, 527],
      (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement520 physical logical agreement) (cons_placements (placement521 physical logical agreement) (cons_placements (placement522 physical logical agreement) (cons_placements (placement523 physical logical agreement) (cons_placements (placement524 physical logical agreement) (cons_placements (placement525 physical logical agreement) (cons_placements (placement526 physical logical agreement) (cons_placements (placement527 physical logical agreement) (by intro index member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
