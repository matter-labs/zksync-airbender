module
public import Proven.Compiler.NativeBridge
public import Proven.Compiler.NativeBindings.Bigint.PlacementData
public import Proven.KernelRfl
public import Human.Compiler.Captures.Bigint
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.Bigint
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- Logical column 72 uses its actual native placement. -/
theorem placement72 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 72 = logical 72 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 72) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[72]'(by decide) = (72, (GKRAddress.BaseLayerWitness 13)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 72 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 13) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 13)) = (GKRAddress.BaseLayerWitness 13) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank72
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 73 uses its actual native placement. -/
theorem placement73 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 73 = logical 73 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 73) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[73]'(by decide) = (73, (GKRAddress.BaseLayerWitness 14)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 73 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 14) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 14)) = (GKRAddress.BaseLayerWitness 14) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank73
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 74 uses its actual native placement. -/
theorem placement74 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 74 = logical 74 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 74) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[74]'(by decide) = (74, (GKRAddress.BaseLayerWitness 15)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 74 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 15) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 15)) = (GKRAddress.BaseLayerWitness 15) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank74
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 75 uses its actual native placement. -/
theorem placement75 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 75 = logical 75 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 75) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[75]'(by decide) = (75, (GKRAddress.BaseLayerWitness 16)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 75 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 16) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 16)) = (GKRAddress.BaseLayerWitness 16) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank75
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 76 uses its actual native placement. -/
theorem placement76 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 76 = logical 76 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 76) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[76]'(by decide) = (76, (GKRAddress.BaseLayerWitness 17)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 76 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 17) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 17)) = (GKRAddress.BaseLayerWitness 17) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank76
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 77 uses its actual native placement. -/
theorem placement77 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 77 = logical 77 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 77) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[77]'(by decide) = (77, (GKRAddress.BaseLayerWitness 18)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 77 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 18) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 18)) = (GKRAddress.BaseLayerWitness 18) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank77
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 78 uses its actual native placement. -/
theorem placement78 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 78 = logical 78 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 78) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[78]'(by decide) = (78, (GKRAddress.BaseLayerWitness 19)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 78 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 19) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 19)) = (GKRAddress.BaseLayerWitness 19) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank78
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 79 uses its actual native placement. -/
theorem placement79 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 79 = logical 79 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 79) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[79]'(by decide) = (79, (GKRAddress.BaseLayerWitness 20)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 79 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 20) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 20)) = (GKRAddress.BaseLayerWitness 20) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank79
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 80 uses its actual native placement. -/
theorem placement80 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 80 = logical 80 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 80) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[80]'(by decide) = (80, (GKRAddress.BaseLayerWitness 21)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 80 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 21) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 21)) = (GKRAddress.BaseLayerWitness 21) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank80
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 81 uses its actual native placement. -/
theorem placement81 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 81 = logical 81 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 81) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[81]'(by decide) = (81, (GKRAddress.BaseLayerWitness 22)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 81 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 22) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 22)) = (GKRAddress.BaseLayerWitness 22) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank81
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 82 uses its actual native placement. -/
theorem placement82 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 82 = logical 82 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 82) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[82]'(by decide) = (82, (GKRAddress.BaseLayerWitness 23)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 82 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 23) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 23)) = (GKRAddress.BaseLayerWitness 23) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank82
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 83 uses its actual native placement. -/
theorem placement83 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 83 = logical 83 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 83) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[83]'(by decide) = (83, (GKRAddress.BaseLayerWitness 24)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 83 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 24) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 24)) = (GKRAddress.BaseLayerWitness 24) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank83
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 84 uses its actual native placement. -/
theorem placement84 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 84 = logical 84 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 84) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[84]'(by decide) = (84, (GKRAddress.BaseLayerWitness 25)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 84 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 25) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 25)) = (GKRAddress.BaseLayerWitness 25) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank84
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 85 uses its actual native placement. -/
theorem placement85 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 85 = logical 85 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 85) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[85]'(by decide) = (85, (GKRAddress.BaseLayerWitness 26)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 85 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 26) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 26)) = (GKRAddress.BaseLayerWitness 26) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank85
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 86 uses its actual native placement. -/
theorem placement86 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 86 = logical 86 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 86) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[86]'(by decide) = (86, (GKRAddress.BaseLayerWitness 27)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 86 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 27) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 27)) = (GKRAddress.BaseLayerWitness 27) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank86
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 87 uses its actual native placement. -/
theorem placement87 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 87 = logical 87 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 87) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[87]'(by decide) = (87, (GKRAddress.BaseLayerWitness 28)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 87 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 28) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 28)) = (GKRAddress.BaseLayerWitness 28) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank87
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 88 uses its actual native placement. -/
theorem placement88 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 88 = logical 88 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 88) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[88]'(by decide) = (88, (GKRAddress.BaseLayerWitness 29)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 88 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 29) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 29)) = (GKRAddress.BaseLayerWitness 29) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank88
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 89 uses its actual native placement. -/
theorem placement89 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 89 = logical 89 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 89) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[89]'(by decide) = (89, (GKRAddress.BaseLayerWitness 30)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 89 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 30) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 30)) = (GKRAddress.BaseLayerWitness 30) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank89
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 90 uses its actual native placement. -/
theorem placement90 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 90 = logical 90 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 90) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[90]'(by decide) = (90, (GKRAddress.BaseLayerWitness 31)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 90 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 31) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 31)) = (GKRAddress.BaseLayerWitness 31) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank90
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 91 uses its actual native placement. -/
theorem placement91 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 91 = logical 91 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 91) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[91]'(by decide) = (91, (GKRAddress.BaseLayerWitness 32)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 91 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 32) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 32)) = (GKRAddress.BaseLayerWitness 32) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank91
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 92 uses its actual native placement. -/
theorem placement92 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 92 = logical 92 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 92) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[92]'(by decide) = (92, (GKRAddress.BaseLayerWitness 33)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 92 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 33) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 33)) = (GKRAddress.BaseLayerWitness 33) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank92
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 93 uses its actual native placement. -/
theorem placement93 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 93 = logical 93 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 93) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[93]'(by decide) = (93, (GKRAddress.BaseLayerWitness 34)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 93 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 34) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 34)) = (GKRAddress.BaseLayerWitness 34) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank93
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 94 uses its actual native placement. -/
theorem placement94 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 94 = logical 94 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 94) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[94]'(by decide) = (94, (GKRAddress.BaseLayerWitness 35)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 94 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 35) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 35)) = (GKRAddress.BaseLayerWitness 35) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank94
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 95 uses its actual native placement. -/
theorem placement95 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 95 = logical 95 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 95) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[95]'(by decide) = (95, (GKRAddress.BaseLayerWitness 36)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 95 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 36) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 36)) = (GKRAddress.BaseLayerWitness 36) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank95
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Public placements cover each column in this batch. -/
theorem placements003 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    ∀ index ∈ [72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95],
      (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement72 physical logical agreement) (cons_placements (placement73 physical logical agreement) (cons_placements (placement74 physical logical agreement) (cons_placements (placement75 physical logical agreement) (cons_placements (placement76 physical logical agreement) (cons_placements (placement77 physical logical agreement) (cons_placements (placement78 physical logical agreement) (cons_placements (placement79 physical logical agreement) (cons_placements (placement80 physical logical agreement) (cons_placements (placement81 physical logical agreement) (cons_placements (placement82 physical logical agreement) (cons_placements (placement83 physical logical agreement) (cons_placements (placement84 physical logical agreement) (cons_placements (placement85 physical logical agreement) (cons_placements (placement86 physical logical agreement) (cons_placements (placement87 physical logical agreement) (cons_placements (placement88 physical logical agreement) (cons_placements (placement89 physical logical agreement) (cons_placements (placement90 physical logical agreement) (cons_placements (placement91 physical logical agreement) (cons_placements (placement92 physical logical agreement) (cons_placements (placement93 physical logical agreement) (cons_placements (placement94 physical logical agreement) (cons_placements (placement95 physical logical agreement) (by intro index member; cases member)))))))))))))))))))))))))
end Airbender.Compiler.NativeBindings.Bigint
