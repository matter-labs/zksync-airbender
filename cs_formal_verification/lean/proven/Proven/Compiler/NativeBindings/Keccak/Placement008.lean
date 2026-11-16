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

/-- Logical column 192 uses its actual native placement. -/
theorem placement192 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 192 = logical 192 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 192) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[192]'(by decide) = (192, (GKRAddress.BaseLayerWitness 129)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 192 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 129) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 129)) = (GKRAddress.BaseLayerWitness 129) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank192
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 193 uses its actual native placement. -/
theorem placement193 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 193 = logical 193 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 193) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[193]'(by decide) = (193, (GKRAddress.BaseLayerWitness 130)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 193 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 130) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 130)) = (GKRAddress.BaseLayerWitness 130) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank193
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 194 uses its actual native placement. -/
theorem placement194 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 194 = logical 194 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 194) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[194]'(by decide) = (194, (GKRAddress.BaseLayerWitness 131)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 194 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 131) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 131)) = (GKRAddress.BaseLayerWitness 131) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank194
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 195 uses its actual native placement. -/
theorem placement195 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 195 = logical 195 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 195) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[195]'(by decide) = (195, (GKRAddress.BaseLayerWitness 132)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 195 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 132) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 132)) = (GKRAddress.BaseLayerWitness 132) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank195
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 196 uses its actual native placement. -/
theorem placement196 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 196 = logical 196 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 196) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[196]'(by decide) = (196, (GKRAddress.BaseLayerWitness 133)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 196 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 133) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 133)) = (GKRAddress.BaseLayerWitness 133) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank196
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 197 uses its actual native placement. -/
theorem placement197 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 197 = logical 197 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 197) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[197]'(by decide) = (197, (GKRAddress.BaseLayerWitness 134)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 197 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 134) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 134)) = (GKRAddress.BaseLayerWitness 134) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank197
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 198 uses its actual native placement. -/
theorem placement198 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 198 = logical 198 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 198) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[198]'(by decide) = (198, (GKRAddress.BaseLayerWitness 135)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 198 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 135) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 135)) = (GKRAddress.BaseLayerWitness 135) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank198
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 199 uses its actual native placement. -/
theorem placement199 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 199 = logical 199 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 199) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[199]'(by decide) = (199, (GKRAddress.BaseLayerWitness 136)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 199 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 136) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 136)) = (GKRAddress.BaseLayerWitness 136) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank199
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 200 uses its actual native placement. -/
theorem placement200 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 200 = logical 200 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 200) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[200]'(by decide) = (200, (GKRAddress.BaseLayerWitness 137)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 200 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 137) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 137)) = (GKRAddress.BaseLayerWitness 137) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank200
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 201 uses its actual native placement. -/
theorem placement201 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 201 = logical 201 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 201) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[201]'(by decide) = (201, (GKRAddress.BaseLayerWitness 138)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 201 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 138) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 138)) = (GKRAddress.BaseLayerWitness 138) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank201
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 202 uses its actual native placement. -/
theorem placement202 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 202 = logical 202 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 202) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[202]'(by decide) = (202, (GKRAddress.BaseLayerWitness 139)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 202 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 139) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 139)) = (GKRAddress.BaseLayerWitness 139) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank202
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 203 uses its actual native placement. -/
theorem placement203 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 203 = logical 203 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 203) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[203]'(by decide) = (203, (GKRAddress.BaseLayerWitness 140)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 203 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 140) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 140)) = (GKRAddress.BaseLayerWitness 140) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank203
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 204 uses its actual native placement. -/
theorem placement204 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 204 = logical 204 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 204) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[204]'(by decide) = (204, (GKRAddress.BaseLayerWitness 141)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 204 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 141) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 141)) = (GKRAddress.BaseLayerWitness 141) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank204
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 205 uses its actual native placement. -/
theorem placement205 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 205 = logical 205 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 205) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[205]'(by decide) = (205, (GKRAddress.BaseLayerWitness 142)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 205 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 142) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 142)) = (GKRAddress.BaseLayerWitness 142) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank205
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 206 uses its actual native placement. -/
theorem placement206 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 206 = logical 206 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 206) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[206]'(by decide) = (206, (GKRAddress.BaseLayerWitness 143)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 206 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 143) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 143)) = (GKRAddress.BaseLayerWitness 143) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank206
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 207 uses its actual native placement. -/
theorem placement207 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 207 = logical 207 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 207) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[207]'(by decide) = (207, (GKRAddress.BaseLayerWitness 144)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 207 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 144) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 144)) = (GKRAddress.BaseLayerWitness 144) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank207
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 208 uses its actual native placement. -/
theorem placement208 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 208 = logical 208 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 208) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[208]'(by decide) = (208, (GKRAddress.BaseLayerWitness 145)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 208 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 145) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 145)) = (GKRAddress.BaseLayerWitness 145) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank208
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 209 uses its actual native placement. -/
theorem placement209 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 209 = logical 209 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 209) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[209]'(by decide) = (209, (GKRAddress.BaseLayerWitness 146)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 209 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 146) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 146)) = (GKRAddress.BaseLayerWitness 146) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank209
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 210 uses its actual native placement. -/
theorem placement210 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 210 = logical 210 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 210) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[210]'(by decide) = (210, (GKRAddress.BaseLayerWitness 147)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 210 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 147) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 147)) = (GKRAddress.BaseLayerWitness 147) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank210
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 211 uses its actual native placement. -/
theorem placement211 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 211 = logical 211 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 211) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[211]'(by decide) = (211, (GKRAddress.BaseLayerWitness 148)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 211 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 148) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 148)) = (GKRAddress.BaseLayerWitness 148) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank211
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 212 uses its actual native placement. -/
theorem placement212 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 212 = logical 212 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 212) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[212]'(by decide) = (212, (GKRAddress.BaseLayerWitness 149)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 212 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 149) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 149)) = (GKRAddress.BaseLayerWitness 149) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank212
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 213 uses its actual native placement. -/
theorem placement213 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 213 = logical 213 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 213) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[213]'(by decide) = (213, (GKRAddress.BaseLayerWitness 150)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 213 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 150) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 150)) = (GKRAddress.BaseLayerWitness 150) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank213
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 214 uses its actual native placement. -/
theorem placement214 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 214 = logical 214 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 214) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[214]'(by decide) = (214, (GKRAddress.BaseLayerWitness 151)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 214 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 151) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 151)) = (GKRAddress.BaseLayerWitness 151) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank214
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 215 uses its actual native placement. -/
theorem placement215 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 215 = logical 215 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 215) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[215]'(by decide) = (215, (GKRAddress.BaseLayerWitness 152)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 215 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 152) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 152)) = (GKRAddress.BaseLayerWitness 152) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank215
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Public placements cover each column in this batch. -/
theorem placements008 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    ∀ index ∈ [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215],
      (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement192 physical logical agreement) (cons_placements (placement193 physical logical agreement) (cons_placements (placement194 physical logical agreement) (cons_placements (placement195 physical logical agreement) (cons_placements (placement196 physical logical agreement) (cons_placements (placement197 physical logical agreement) (cons_placements (placement198 physical logical agreement) (cons_placements (placement199 physical logical agreement) (cons_placements (placement200 physical logical agreement) (cons_placements (placement201 physical logical agreement) (cons_placements (placement202 physical logical agreement) (cons_placements (placement203 physical logical agreement) (cons_placements (placement204 physical logical agreement) (cons_placements (placement205 physical logical agreement) (cons_placements (placement206 physical logical agreement) (cons_placements (placement207 physical logical agreement) (cons_placements (placement208 physical logical agreement) (cons_placements (placement209 physical logical agreement) (cons_placements (placement210 physical logical agreement) (cons_placements (placement211 physical logical agreement) (cons_placements (placement212 physical logical agreement) (cons_placements (placement213 physical logical agreement) (cons_placements (placement214 physical logical agreement) (cons_placements (placement215 physical logical agreement) (by intro index member; cases member)))))))))))))))))))))))))
end Airbender.Compiler.NativeBindings.Keccak
