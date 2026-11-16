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

/-- Logical column 24 uses its actual native placement. -/
theorem placement24 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 24 = logical 24 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 24) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[24]'(by decide) = (24, (GKRAddress.BaseLayerMemory 26)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 24 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 26) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 26)) = (GKRAddress.BaseLayerMemory 26) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank24
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 25 uses its actual native placement. -/
theorem placement25 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 25 = logical 25 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 25) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[25]'(by decide) = (25, (GKRAddress.BaseLayerMemory 28)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 25 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 28) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 28)) = (GKRAddress.BaseLayerMemory 28) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank25
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 26 uses its actual native placement. -/
theorem placement26 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 26 = logical 26 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 26) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[26]'(by decide) = (26, (GKRAddress.BaseLayerMemory 29)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 26 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 29) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 29)) = (GKRAddress.BaseLayerMemory 29) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank26
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 27 uses its actual native placement. -/
theorem placement27 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 27 = logical 27 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 27) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[27]'(by decide) = (27, (GKRAddress.BaseLayerMemory 32)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 27 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 32) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 32)) = (GKRAddress.BaseLayerMemory 32) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank27
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 28 uses its actual native placement. -/
theorem placement28 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 28 = logical 28 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 28) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[28]'(by decide) = (28, (GKRAddress.BaseLayerMemory 33)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 28 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 33) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 33)) = (GKRAddress.BaseLayerMemory 33) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank28
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 29 uses its actual native placement. -/
theorem placement29 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 29 = logical 29 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 29) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[29]'(by decide) = (29, (GKRAddress.BaseLayerMemory 34)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 29 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 34) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 34)) = (GKRAddress.BaseLayerMemory 34) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank29
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 30 uses its actual native placement. -/
theorem placement30 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 30 = logical 30 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 30) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[30]'(by decide) = (30, (GKRAddress.BaseLayerMemory 35)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 30 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 35) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 35)) = (GKRAddress.BaseLayerMemory 35) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank30
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 31 uses its actual native placement. -/
theorem placement31 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 31 = logical 31 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 31) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[31]'(by decide) = (31, (GKRAddress.BaseLayerMemory 38)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 31 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 38) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 38)) = (GKRAddress.BaseLayerMemory 38) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank31
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 32 uses its actual native placement. -/
theorem placement32 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 32 = logical 32 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 32) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[32]'(by decide) = (32, (GKRAddress.BaseLayerMemory 39)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 32 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 39) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 39)) = (GKRAddress.BaseLayerMemory 39) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank32
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 33 uses its actual native placement. -/
theorem placement33 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 33 = logical 33 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 33) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[33]'(by decide) = (33, (GKRAddress.BaseLayerMemory 41)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 33 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 41) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 41)) = (GKRAddress.BaseLayerMemory 41) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank33
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 34 uses its actual native placement. -/
theorem placement34 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 34 = logical 34 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 34) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[34]'(by decide) = (34, (GKRAddress.BaseLayerMemory 42)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 34 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 42) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 42)) = (GKRAddress.BaseLayerMemory 42) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank34
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 35 uses its actual native placement. -/
theorem placement35 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 35 = logical 35 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 35) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[35]'(by decide) = (35, (GKRAddress.BaseLayerMemory 45)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 35 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 45) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 45)) = (GKRAddress.BaseLayerMemory 45) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank35
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 36 uses its actual native placement. -/
theorem placement36 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 36 = logical 36 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 36) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[36]'(by decide) = (36, (GKRAddress.BaseLayerMemory 46)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 36 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 46) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 46)) = (GKRAddress.BaseLayerMemory 46) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank36
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 37 uses its actual native placement. -/
theorem placement37 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 37 = logical 37 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 37) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[37]'(by decide) = (37, (GKRAddress.BaseLayerMemory 47)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 37 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 47) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 47)) = (GKRAddress.BaseLayerMemory 47) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank37
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 38 uses its actual native placement. -/
theorem placement38 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 38 = logical 38 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 38) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[38]'(by decide) = (38, (GKRAddress.BaseLayerMemory 48)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 38 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 48) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 48)) = (GKRAddress.BaseLayerMemory 48) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank38
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 39 uses its actual native placement. -/
theorem placement39 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 39 = logical 39 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 39) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[39]'(by decide) = (39, (GKRAddress.BaseLayerMemory 51)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 39 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 51) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 51)) = (GKRAddress.BaseLayerMemory 51) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank39
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 40 uses its actual native placement. -/
theorem placement40 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 40 = logical 40 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 40) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[40]'(by decide) = (40, (GKRAddress.BaseLayerMemory 52)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 40 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 52) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 52)) = (GKRAddress.BaseLayerMemory 52) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank40
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 41 uses its actual native placement. -/
theorem placement41 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 41 = logical 41 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 41) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[41]'(by decide) = (41, (GKRAddress.BaseLayerMemory 54)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 41 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 54) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 54)) = (GKRAddress.BaseLayerMemory 54) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank41
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 42 uses its actual native placement. -/
theorem placement42 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 42 = logical 42 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 42) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[42]'(by decide) = (42, (GKRAddress.BaseLayerMemory 55)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 42 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 55) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 55)) = (GKRAddress.BaseLayerMemory 55) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank42
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 43 uses its actual native placement. -/
theorem placement43 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 43 = logical 43 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 43) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[43]'(by decide) = (43, (GKRAddress.BaseLayerMemory 58)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 43 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 58) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 58)) = (GKRAddress.BaseLayerMemory 58) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank43
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 44 uses its actual native placement. -/
theorem placement44 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 44 = logical 44 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 44) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[44]'(by decide) = (44, (GKRAddress.BaseLayerMemory 59)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 44 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 59) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 59)) = (GKRAddress.BaseLayerMemory 59) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank44
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 45 uses its actual native placement. -/
theorem placement45 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 45 = logical 45 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 45) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[45]'(by decide) = (45, (GKRAddress.BaseLayerMemory 60)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 45 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 60) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 60)) = (GKRAddress.BaseLayerMemory 60) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank45
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 46 uses its actual native placement. -/
theorem placement46 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 46 = logical 46 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 46) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[46]'(by decide) = (46, (GKRAddress.BaseLayerMemory 61)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 46 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 61) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 61)) = (GKRAddress.BaseLayerMemory 61) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank46
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 47 uses its actual native placement. -/
theorem placement47 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 47 = logical 47 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 47) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[47]'(by decide) = (47, (GKRAddress.BaseLayerMemory 64)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 47 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 64) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerMemory 64)) = (GKRAddress.BaseLayerMemory 64) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank47
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Public placements cover each column in this batch. -/
theorem placements001 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    ∀ index ∈ [24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47],
      (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement24 physical logical agreement) (cons_placements (placement25 physical logical agreement) (cons_placements (placement26 physical logical agreement) (cons_placements (placement27 physical logical agreement) (cons_placements (placement28 physical logical agreement) (cons_placements (placement29 physical logical agreement) (cons_placements (placement30 physical logical agreement) (cons_placements (placement31 physical logical agreement) (cons_placements (placement32 physical logical agreement) (cons_placements (placement33 physical logical agreement) (cons_placements (placement34 physical logical agreement) (cons_placements (placement35 physical logical agreement) (cons_placements (placement36 physical logical agreement) (cons_placements (placement37 physical logical agreement) (cons_placements (placement38 physical logical agreement) (cons_placements (placement39 physical logical agreement) (cons_placements (placement40 physical logical agreement) (cons_placements (placement41 physical logical agreement) (cons_placements (placement42 physical logical agreement) (cons_placements (placement43 physical logical agreement) (cons_placements (placement44 physical logical agreement) (cons_placements (placement45 physical logical agreement) (cons_placements (placement46 physical logical agreement) (cons_placements (placement47 physical logical agreement) (by intro index member; cases member)))))))))))))))))))))))))
end Airbender.Compiler.NativeBindings.Keccak
