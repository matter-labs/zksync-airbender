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

/-- Logical column 24 uses its actual native placement. -/
theorem placement24 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 24 = logical 24 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 24) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[24]'(by decide) = (24, (GKRAddress.BaseLayerMemory 33)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 24 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 33) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 33)) = (GKRAddress.BaseLayerMemory 33) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank24
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 25 uses its actual native placement. -/
theorem placement25 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 25 = logical 25 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 25) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[25]'(by decide) = (25, (GKRAddress.BaseLayerMemory 36)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 25 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 36) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 36)) = (GKRAddress.BaseLayerMemory 36) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank25
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 26 uses its actual native placement. -/
theorem placement26 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 26 = logical 26 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 26) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[26]'(by decide) = (26, (GKRAddress.BaseLayerMemory 37)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 26 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 37) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 37)) = (GKRAddress.BaseLayerMemory 37) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank26
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 27 uses its actual native placement. -/
theorem placement27 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 27 = logical 27 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 27) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[27]'(by decide) = (27, (GKRAddress.BaseLayerMemory 38)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 27 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 38) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 38)) = (GKRAddress.BaseLayerMemory 38) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank27
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 28 uses its actual native placement. -/
theorem placement28 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 28 = logical 28 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 28) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[28]'(by decide) = (28, (GKRAddress.BaseLayerMemory 39)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 28 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 39) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 39)) = (GKRAddress.BaseLayerMemory 39) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank28
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 29 uses its actual native placement. -/
theorem placement29 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 29 = logical 29 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 29) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[29]'(by decide) = (29, (GKRAddress.BaseLayerMemory 42)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 29 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 42) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 42)) = (GKRAddress.BaseLayerMemory 42) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank29
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 30 uses its actual native placement. -/
theorem placement30 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 30 = logical 30 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 30) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[30]'(by decide) = (30, (GKRAddress.BaseLayerMemory 43)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 30 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 43) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 43)) = (GKRAddress.BaseLayerMemory 43) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank30
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 31 uses its actual native placement. -/
theorem placement31 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 31 = logical 31 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 31) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[31]'(by decide) = (31, (GKRAddress.BaseLayerMemory 44)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 31 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 44) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 44)) = (GKRAddress.BaseLayerMemory 44) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank31
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Public placements cover each column in this batch. -/
theorem placements003 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    ∀ index ∈ [24, 25, 26, 27, 28, 29, 30, 31],
      (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement24 physical logical agreement) (cons_placements (placement25 physical logical agreement) (cons_placements (placement26 physical logical agreement) (cons_placements (placement27 physical logical agreement) (cons_placements (placement28 physical logical agreement) (cons_placements (placement29 physical logical agreement) (cons_placements (placement30 physical logical agreement) (cons_placements (placement31 physical logical agreement) (by intro index member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
