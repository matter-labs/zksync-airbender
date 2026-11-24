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

/-- Logical column 144 uses its actual native placement. -/
theorem placement144 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 144 = logical 144 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 144) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[144]'(by decide) = (144, (GKRAddress.BaseLayerWitness 81)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 144 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 81) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 81)) = (GKRAddress.BaseLayerWitness 81) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank144
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 145 uses its actual native placement. -/
theorem placement145 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 145 = logical 145 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 145) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[145]'(by decide) = (145, (GKRAddress.BaseLayerWitness 82)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 145 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 82) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 82)) = (GKRAddress.BaseLayerWitness 82) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank145
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 146 uses its actual native placement. -/
theorem placement146 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 146 = logical 146 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 146) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[146]'(by decide) = (146, (GKRAddress.BaseLayerWitness 83)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 146 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 83) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 83)) = (GKRAddress.BaseLayerWitness 83) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank146
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 147 uses its actual native placement. -/
theorem placement147 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 147 = logical 147 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 147) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[147]'(by decide) = (147, (GKRAddress.BaseLayerWitness 84)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 147 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 84) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 84)) = (GKRAddress.BaseLayerWitness 84) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank147
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 148 uses its actual native placement. -/
theorem placement148 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 148 = logical 148 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 148) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[148]'(by decide) = (148, (GKRAddress.BaseLayerWitness 85)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 148 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 85) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 85)) = (GKRAddress.BaseLayerWitness 85) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank148
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 149 uses its actual native placement. -/
theorem placement149 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 149 = logical 149 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 149) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[149]'(by decide) = (149, (GKRAddress.BaseLayerWitness 86)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 149 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 86) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 86)) = (GKRAddress.BaseLayerWitness 86) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank149
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 150 uses its actual native placement. -/
theorem placement150 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 150 = logical 150 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 150) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[150]'(by decide) = (150, (GKRAddress.BaseLayerWitness 87)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 150 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 87) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 87)) = (GKRAddress.BaseLayerWitness 87) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank150
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 151 uses its actual native placement. -/
theorem placement151 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 151 = logical 151 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 151) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[151]'(by decide) = (151, (GKRAddress.BaseLayerWitness 88)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 151 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 88) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 88)) = (GKRAddress.BaseLayerWitness 88) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank151
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 152 uses its actual native placement. -/
theorem placement152 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 152 = logical 152 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 152) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[152]'(by decide) = (152, (GKRAddress.BaseLayerWitness 89)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 152 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 89) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 89)) = (GKRAddress.BaseLayerWitness 89) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank152
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 153 uses its actual native placement. -/
theorem placement153 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 153 = logical 153 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 153) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[153]'(by decide) = (153, (GKRAddress.BaseLayerWitness 90)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 153 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 90) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 90)) = (GKRAddress.BaseLayerWitness 90) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank153
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 154 uses its actual native placement. -/
theorem placement154 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 154 = logical 154 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 154) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[154]'(by decide) = (154, (GKRAddress.BaseLayerWitness 91)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 154 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 91) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 91)) = (GKRAddress.BaseLayerWitness 91) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank154
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 155 uses its actual native placement. -/
theorem placement155 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 155 = logical 155 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 155) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[155]'(by decide) = (155, (GKRAddress.BaseLayerWitness 92)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 155 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 92) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 92)) = (GKRAddress.BaseLayerWitness 92) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank155
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 156 uses its actual native placement. -/
theorem placement156 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 156 = logical 156 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 156) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[156]'(by decide) = (156, (GKRAddress.BaseLayerWitness 93)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 156 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 93) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 93)) = (GKRAddress.BaseLayerWitness 93) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank156
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 157 uses its actual native placement. -/
theorem placement157 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 157 = logical 157 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 157) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[157]'(by decide) = (157, (GKRAddress.BaseLayerWitness 94)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 157 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 94) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 94)) = (GKRAddress.BaseLayerWitness 94) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank157
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 158 uses its actual native placement. -/
theorem placement158 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 158 = logical 158 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 158) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[158]'(by decide) = (158, (GKRAddress.BaseLayerWitness 95)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 158 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 95) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 95)) = (GKRAddress.BaseLayerWitness 95) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank158
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 159 uses its actual native placement. -/
theorem placement159 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 159 = logical 159 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 159) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[159]'(by decide) = (159, (GKRAddress.BaseLayerWitness 96)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 159 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 96) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 96)) = (GKRAddress.BaseLayerWitness 96) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank159
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 160 uses its actual native placement. -/
theorem placement160 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 160 = logical 160 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 160) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[160]'(by decide) = (160, (GKRAddress.BaseLayerWitness 97)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 160 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 97) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 97)) = (GKRAddress.BaseLayerWitness 97) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank160
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 161 uses its actual native placement. -/
theorem placement161 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 161 = logical 161 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 161) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[161]'(by decide) = (161, (GKRAddress.BaseLayerWitness 98)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 161 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 98) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 98)) = (GKRAddress.BaseLayerWitness 98) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank161
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 162 uses its actual native placement. -/
theorem placement162 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 162 = logical 162 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 162) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[162]'(by decide) = (162, (GKRAddress.BaseLayerWitness 99)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 162 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 99) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 99)) = (GKRAddress.BaseLayerWitness 99) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank162
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 163 uses its actual native placement. -/
theorem placement163 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 163 = logical 163 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 163) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[163]'(by decide) = (163, (GKRAddress.BaseLayerWitness 100)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 163 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 100) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 100)) = (GKRAddress.BaseLayerWitness 100) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank163
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 164 uses its actual native placement. -/
theorem placement164 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 164 = logical 164 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 164) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[164]'(by decide) = (164, (GKRAddress.BaseLayerWitness 101)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 164 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 101) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 101)) = (GKRAddress.BaseLayerWitness 101) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank164
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 165 uses its actual native placement. -/
theorem placement165 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 165 = logical 165 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 165) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[165]'(by decide) = (165, (GKRAddress.BaseLayerWitness 102)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 165 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 102) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 102)) = (GKRAddress.BaseLayerWitness 102) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank165
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 166 uses its actual native placement. -/
theorem placement166 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 166 = logical 166 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 166) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[166]'(by decide) = (166, (GKRAddress.BaseLayerWitness 103)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 166 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 103) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 103)) = (GKRAddress.BaseLayerWitness 103) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank166
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 167 uses its actual native placement. -/
theorem placement167 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 167 = logical 167 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 167) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[167]'(by decide) = (167, (GKRAddress.BaseLayerWitness 104)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 167 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 104) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 104)) = (GKRAddress.BaseLayerWitness 104) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank167
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Public placements cover each column in this batch. -/
theorem placements006 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    ∀ index ∈ [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167],
      (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement144 physical logical agreement) (cons_placements (placement145 physical logical agreement) (cons_placements (placement146 physical logical agreement) (cons_placements (placement147 physical logical agreement) (cons_placements (placement148 physical logical agreement) (cons_placements (placement149 physical logical agreement) (cons_placements (placement150 physical logical agreement) (cons_placements (placement151 physical logical agreement) (cons_placements (placement152 physical logical agreement) (cons_placements (placement153 physical logical agreement) (cons_placements (placement154 physical logical agreement) (cons_placements (placement155 physical logical agreement) (cons_placements (placement156 physical logical agreement) (cons_placements (placement157 physical logical agreement) (cons_placements (placement158 physical logical agreement) (cons_placements (placement159 physical logical agreement) (cons_placements (placement160 physical logical agreement) (cons_placements (placement161 physical logical agreement) (cons_placements (placement162 physical logical agreement) (cons_placements (placement163 physical logical agreement) (cons_placements (placement164 physical logical agreement) (cons_placements (placement165 physical logical agreement) (cons_placements (placement166 physical logical agreement) (cons_placements (placement167 physical logical agreement) (by intro index member; cases member)))))))))))))))))))))))))
end Airbender.Compiler.NativeBindings.Keccak
