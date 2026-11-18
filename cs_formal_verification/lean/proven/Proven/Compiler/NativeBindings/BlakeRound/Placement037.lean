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

/-- Logical column 296 uses its actual native placement. -/
theorem placement296 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 296 = logical 296 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 296) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[296]'(by decide) = (296, (GKRAddress.BaseLayerWitness 157)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 296 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 157) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 157)) = (GKRAddress.BaseLayerWitness 157) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank296
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 297 uses its actual native placement. -/
theorem placement297 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 297 = logical 297 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 297) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[297]'(by decide) = (297, (GKRAddress.BaseLayerWitness 158)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 297 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 158) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 158)) = (GKRAddress.BaseLayerWitness 158) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank297
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 298 uses its actual native placement. -/
theorem placement298 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 298 = logical 298 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 298) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[298]'(by decide) = (298, (GKRAddress.BaseLayerWitness 159)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 298 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 159) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 159)) = (GKRAddress.BaseLayerWitness 159) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank298
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 299 uses its actual native placement. -/
theorem placement299 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 299 = logical 299 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 299) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[299]'(by decide) = (299, (GKRAddress.BaseLayerWitness 160)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 299 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 160) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 160)) = (GKRAddress.BaseLayerWitness 160) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank299
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 300 uses its actual native placement. -/
theorem placement300 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 300 = logical 300 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 300) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[300]'(by decide) = (300, (GKRAddress.BaseLayerWitness 161)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 300 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 161) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 161)) = (GKRAddress.BaseLayerWitness 161) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank300
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 301 uses its actual native placement. -/
theorem placement301 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 301 = logical 301 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 301) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[301]'(by decide) = (301, (GKRAddress.BaseLayerWitness 162)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 301 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 162) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 162)) = (GKRAddress.BaseLayerWitness 162) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank301
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 302 uses its actual native placement. -/
theorem placement302 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 302 = logical 302 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 302) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[302]'(by decide) = (302, (GKRAddress.BaseLayerWitness 163)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 302 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 163) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 163)) = (GKRAddress.BaseLayerWitness 163) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank302
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 303 uses its actual native placement. -/
theorem placement303 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 303 = logical 303 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 303) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[303]'(by decide) = (303, (GKRAddress.BaseLayerWitness 164)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 303 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 164) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 164)) = (GKRAddress.BaseLayerWitness 164) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank303
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Public placements cover each column in this batch. -/
theorem placements037 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    ∀ index ∈ [296, 297, 298, 299, 300, 301, 302, 303],
      (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement296 physical logical agreement) (cons_placements (placement297 physical logical agreement) (cons_placements (placement298 physical logical agreement) (cons_placements (placement299 physical logical agreement) (cons_placements (placement300 physical logical agreement) (cons_placements (placement301 physical logical agreement) (cons_placements (placement302 physical logical agreement) (cons_placements (placement303 physical logical agreement) (by intro index member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
