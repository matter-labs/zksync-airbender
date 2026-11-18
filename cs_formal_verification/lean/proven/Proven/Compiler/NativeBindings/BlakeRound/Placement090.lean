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

/-- Logical column 720 uses its actual native placement. -/
theorem placement720 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 720 = logical 720 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 720) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[720]'(by decide) = (720, (GKRAddress.BaseLayerMemory 165)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 720 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 165) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 165)) = (GKRAddress.BaseLayerMemory 165) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank720
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 721 uses its actual native placement. -/
theorem placement721 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 721 = logical 721 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 721) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[721]'(by decide) = (721, (GKRAddress.BaseLayerWitness 522)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 721 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 522) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 522)) = (GKRAddress.BaseLayerWitness 522) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank721
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 722 uses its actual native placement. -/
theorem placement722 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 722 = logical 722 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 722) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[722]'(by decide) = (722, (GKRAddress.BaseLayerMemory 168)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 722 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 168) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 168)) = (GKRAddress.BaseLayerMemory 168) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank722
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 723 uses its actual native placement. -/
theorem placement723 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 723 = logical 723 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 723) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[723]'(by decide) = (723, (GKRAddress.BaseLayerMemory 169)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 723 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 169) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 169)) = (GKRAddress.BaseLayerMemory 169) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank723
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 724 uses its actual native placement. -/
theorem placement724 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 724 = logical 724 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 724) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[724]'(by decide) = (724, (GKRAddress.BaseLayerWitness 523)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 724 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 523) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 523)) = (GKRAddress.BaseLayerWitness 523) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank724
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 725 uses its actual native placement. -/
theorem placement725 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 725 = logical 725 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 725) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[725]'(by decide) = (725, (GKRAddress.BaseLayerMemory 172)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 725 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 172) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 172)) = (GKRAddress.BaseLayerMemory 172) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank725
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 726 uses its actual native placement. -/
theorem placement726 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 726 = logical 726 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 726) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[726]'(by decide) = (726, (GKRAddress.BaseLayerMemory 173)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 726 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 173) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerMemory 173)) = (GKRAddress.BaseLayerMemory 173) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank726
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 727 uses its actual native placement. -/
theorem placement727 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 727 = logical 727 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 727) (by decide)
  have captured : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[727]'(by decide) = (727, (GKRAddress.BaseLayerWitness 524)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 727 = Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 524) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.placement (GKRAddress.BaseLayerWitness 524)) = (GKRAddress.BaseLayerWitness 524) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placementInBank727
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Public placements cover each column in this batch. -/
theorem placements090 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    ∀ index ∈ [720, 721, 722, 723, 724, 725, 726, 727],
      (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement720 physical logical agreement) (cons_placements (placement721 physical logical agreement) (cons_placements (placement722 physical logical agreement) (cons_placements (placement723 physical logical agreement) (cons_placements (placement724 physical logical agreement) (cons_placements (placement725 physical logical agreement) (cons_placements (placement726 physical logical agreement) (cons_placements (placement727 physical logical agreement) (by intro index member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
