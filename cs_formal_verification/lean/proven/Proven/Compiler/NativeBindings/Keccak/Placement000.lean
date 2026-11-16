module
public import Proven.Compiler.NativeBridge
public import Proven.Compiler.NativeBindings.Keccak.PlacementData
public import Proven.KernelRfl
public import Human.Compiler.Captures.Keccak
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.Keccak
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- Logical column 0 uses its actual native placement. -/
theorem placement0 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 0 = logical 0 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 0) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[0]'(by decide) = (0, (GKRAddress.BaseLayerMemory 88)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 0 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 88) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 88)) = (GKRAddress.BaseLayerMemory 88) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank0
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 1 uses its actual native placement. -/
theorem placement1 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 1 = logical 1 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 1) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[1]'(by decide) = (1, (GKRAddress.BaseLayerMemory 89)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 1 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 89) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 89)) = (GKRAddress.BaseLayerMemory 89) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank1
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 2 uses its actual native placement. -/
theorem placement2 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 2 = logical 2 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 2) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[2]'(by decide) = (2, (GKRAddress.BaseLayerMemory 90)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 2 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 90) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 90)) = (GKRAddress.BaseLayerMemory 90) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank2
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 3 uses its actual native placement. -/
theorem placement3 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 3 = logical 3 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 3) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[3]'(by decide) = (3, (GKRAddress.BaseLayerMemory 2)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 3 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 2) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 2)) = (GKRAddress.BaseLayerMemory 2) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank3
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 4 uses its actual native placement. -/
theorem placement4 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 4 = logical 4 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 4) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[4]'(by decide) = (4, (GKRAddress.BaseLayerMemory 3)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 4 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 3) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 3)) = (GKRAddress.BaseLayerMemory 3) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank4
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 5 uses its actual native placement. -/
theorem placement5 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 5 = logical 5 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 5) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[5]'(by decide) = (5, (GKRAddress.BaseLayerMemory 4)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 5 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 4) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 4)) = (GKRAddress.BaseLayerMemory 4) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank5
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 6 uses its actual native placement. -/
theorem placement6 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 6 = logical 6 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 6) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[6]'(by decide) = (6, (GKRAddress.BaseLayerMemory 5)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 6 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 5) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 5)) = (GKRAddress.BaseLayerMemory 5) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank6
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 7 uses its actual native placement. -/
theorem placement7 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 7 = logical 7 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 7) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[7]'(by decide) = (7, (GKRAddress.BaseLayerMemory 14)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 7 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 14) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 14)) = (GKRAddress.BaseLayerMemory 14) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank7
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 8 uses its actual native placement. -/
theorem placement8 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 8 = logical 8 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 8) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[8]'(by decide) = (8, (GKRAddress.BaseLayerMemory 27)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 8 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 27) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 27)) = (GKRAddress.BaseLayerMemory 27) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank8
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 9 uses its actual native placement. -/
theorem placement9 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 9 = logical 9 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 9) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[9]'(by decide) = (9, (GKRAddress.BaseLayerMemory 40)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 9 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 40) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 40)) = (GKRAddress.BaseLayerMemory 40) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank9
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 10 uses its actual native placement. -/
theorem placement10 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 10 = logical 10 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 10) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[10]'(by decide) = (10, (GKRAddress.BaseLayerMemory 53)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 10 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 53) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 53)) = (GKRAddress.BaseLayerMemory 53) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank10
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 11 uses its actual native placement. -/
theorem placement11 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 11 = logical 11 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 11) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[11]'(by decide) = (11, (GKRAddress.BaseLayerMemory 66)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 11 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 66) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 66)) = (GKRAddress.BaseLayerMemory 66) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank11
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 12 uses its actual native placement. -/
theorem placement12 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 12 = logical 12 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 12) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[12]'(by decide) = (12, (GKRAddress.BaseLayerMemory 79)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 12 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 79) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 79)) = (GKRAddress.BaseLayerMemory 79) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank12
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 13 uses its actual native placement. -/
theorem placement13 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 13 = logical 13 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 13) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[13]'(by decide) = (13, (GKRAddress.BaseLayerMemory 8)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 13 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 8) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 8)) = (GKRAddress.BaseLayerMemory 8) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank13
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 14 uses its actual native placement. -/
theorem placement14 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 14 = logical 14 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 14) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[14]'(by decide) = (14, (GKRAddress.BaseLayerMemory 9)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 14 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 9) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 9)) = (GKRAddress.BaseLayerMemory 9) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank14
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 15 uses its actual native placement. -/
theorem placement15 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 15 = logical 15 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 15) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[15]'(by decide) = (15, (GKRAddress.BaseLayerMemory 12)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 15 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 12) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 12)) = (GKRAddress.BaseLayerMemory 12) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank15
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 16 uses its actual native placement. -/
theorem placement16 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 16 = logical 16 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 16) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[16]'(by decide) = (16, (GKRAddress.BaseLayerMemory 13)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 16 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 13) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 13)) = (GKRAddress.BaseLayerMemory 13) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank16
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 17 uses its actual native placement. -/
theorem placement17 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 17 = logical 17 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 17) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[17]'(by decide) = (17, (GKRAddress.BaseLayerMemory 15)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 17 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 15) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 15)) = (GKRAddress.BaseLayerMemory 15) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank17
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 18 uses its actual native placement. -/
theorem placement18 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 18 = logical 18 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 18) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[18]'(by decide) = (18, (GKRAddress.BaseLayerMemory 16)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 18 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 16) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 16)) = (GKRAddress.BaseLayerMemory 16) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank18
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 19 uses its actual native placement. -/
theorem placement19 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 19 = logical 19 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 19) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[19]'(by decide) = (19, (GKRAddress.BaseLayerMemory 19)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 19 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 19) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 19)) = (GKRAddress.BaseLayerMemory 19) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank19
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 20 uses its actual native placement. -/
theorem placement20 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 20 = logical 20 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 20) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[20]'(by decide) = (20, (GKRAddress.BaseLayerMemory 20)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 20 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 20) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 20)) = (GKRAddress.BaseLayerMemory 20) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank20
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 21 uses its actual native placement. -/
theorem placement21 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 21 = logical 21 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 21) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[21]'(by decide) = (21, (GKRAddress.BaseLayerMemory 21)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 21 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 21) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 21)) = (GKRAddress.BaseLayerMemory 21) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank21
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 22 uses its actual native placement. -/
theorem placement22 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 22 = logical 22 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 22) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[22]'(by decide) = (22, (GKRAddress.BaseLayerMemory 22)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 22 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 22) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 22)) = (GKRAddress.BaseLayerMemory 22) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank22
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 23 uses its actual native placement. -/
theorem placement23 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 23 = logical 23 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 23) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[23]'(by decide) = (23, (GKRAddress.BaseLayerMemory 25)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 23 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 25) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 25)) = (GKRAddress.BaseLayerMemory 25) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank23
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Public placements cover each column in this batch. -/
theorem placements000 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    ∀ index ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
      (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement0 physical logical agreement) (cons_placements (placement1 physical logical agreement) (cons_placements (placement2 physical logical agreement) (cons_placements (placement3 physical logical agreement) (cons_placements (placement4 physical logical agreement) (cons_placements (placement5 physical logical agreement) (cons_placements (placement6 physical logical agreement) (cons_placements (placement7 physical logical agreement) (cons_placements (placement8 physical logical agreement) (cons_placements (placement9 physical logical agreement) (cons_placements (placement10 physical logical agreement) (cons_placements (placement11 physical logical agreement) (cons_placements (placement12 physical logical agreement) (cons_placements (placement13 physical logical agreement) (cons_placements (placement14 physical logical agreement) (cons_placements (placement15 physical logical agreement) (cons_placements (placement16 physical logical agreement) (cons_placements (placement17 physical logical agreement) (cons_placements (placement18 physical logical agreement) (cons_placements (placement19 physical logical agreement) (cons_placements (placement20 physical logical agreement) (cons_placements (placement21 physical logical agreement) (cons_placements (placement22 physical logical agreement) (cons_placements (placement23 physical logical agreement) (by intro index member; cases member)))))))))))))))))))))))))
end Airbender.Compiler.NativeBindings.Keccak
