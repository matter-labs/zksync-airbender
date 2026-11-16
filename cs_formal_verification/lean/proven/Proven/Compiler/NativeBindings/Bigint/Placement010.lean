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

/-- Logical column 240 uses its actual native placement. -/
theorem placement240 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 240 = logical 240 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 240) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[240]'(by decide) = (240, (GKRAddress.BaseLayerMemory 46)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 240 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 46) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 46)) = (GKRAddress.BaseLayerMemory 46) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank240
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 241 uses its actual native placement. -/
theorem placement241 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 241 = logical 241 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 241) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[241]'(by decide) = (241, (GKRAddress.BaseLayerMemory 47)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 241 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 47) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 47)) = (GKRAddress.BaseLayerMemory 47) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank241
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 242 uses its actual native placement. -/
theorem placement242 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 242 = logical 242 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 242) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[242]'(by decide) = (242, (GKRAddress.BaseLayerWitness 146)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 242 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 146) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 146)) = (GKRAddress.BaseLayerWitness 146) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank242
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 243 uses its actual native placement. -/
theorem placement243 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 243 = logical 243 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 243) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[243]'(by decide) = (243, (GKRAddress.BaseLayerMemory 52)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 243 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 52) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 52)) = (GKRAddress.BaseLayerMemory 52) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank243
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 244 uses its actual native placement. -/
theorem placement244 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 244 = logical 244 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 244) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[244]'(by decide) = (244, (GKRAddress.BaseLayerMemory 53)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 244 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 53) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 53)) = (GKRAddress.BaseLayerMemory 53) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank244
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 245 uses its actual native placement. -/
theorem placement245 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 245 = logical 245 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 245) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[245]'(by decide) = (245, (GKRAddress.BaseLayerWitness 147)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 245 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 147) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 147)) = (GKRAddress.BaseLayerWitness 147) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank245
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 246 uses its actual native placement. -/
theorem placement246 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 246 = logical 246 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 246) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[246]'(by decide) = (246, (GKRAddress.BaseLayerMemory 56)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 246 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 56) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 56)) = (GKRAddress.BaseLayerMemory 56) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank246
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 247 uses its actual native placement. -/
theorem placement247 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 247 = logical 247 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 247) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[247]'(by decide) = (247, (GKRAddress.BaseLayerMemory 57)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 247 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 57) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 57)) = (GKRAddress.BaseLayerMemory 57) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank247
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 248 uses its actual native placement. -/
theorem placement248 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 248 = logical 248 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 248) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[248]'(by decide) = (248, (GKRAddress.BaseLayerWitness 148)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 248 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 148) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 148)) = (GKRAddress.BaseLayerWitness 148) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank248
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 249 uses its actual native placement. -/
theorem placement249 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 249 = logical 249 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 249) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[249]'(by decide) = (249, (GKRAddress.BaseLayerMemory 60)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 249 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 60) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 60)) = (GKRAddress.BaseLayerMemory 60) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank249
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 250 uses its actual native placement. -/
theorem placement250 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 250 = logical 250 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 250) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[250]'(by decide) = (250, (GKRAddress.BaseLayerMemory 61)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 250 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 61) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 61)) = (GKRAddress.BaseLayerMemory 61) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank250
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 251 uses its actual native placement. -/
theorem placement251 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 251 = logical 251 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 251) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[251]'(by decide) = (251, (GKRAddress.BaseLayerWitness 149)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 251 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 149) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 149)) = (GKRAddress.BaseLayerWitness 149) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank251
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 252 uses its actual native placement. -/
theorem placement252 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 252 = logical 252 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 252) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[252]'(by decide) = (252, (GKRAddress.BaseLayerMemory 64)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 252 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 64) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 64)) = (GKRAddress.BaseLayerMemory 64) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank252
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 253 uses its actual native placement. -/
theorem placement253 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 253 = logical 253 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 253) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[253]'(by decide) = (253, (GKRAddress.BaseLayerMemory 65)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 253 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 65) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 65)) = (GKRAddress.BaseLayerMemory 65) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank253
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 254 uses its actual native placement. -/
theorem placement254 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 254 = logical 254 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 254) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[254]'(by decide) = (254, (GKRAddress.BaseLayerWitness 150)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 254 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 150) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 150)) = (GKRAddress.BaseLayerWitness 150) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank254
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 255 uses its actual native placement. -/
theorem placement255 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 255 = logical 255 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 255) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[255]'(by decide) = (255, (GKRAddress.BaseLayerMemory 68)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 255 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 68) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 68)) = (GKRAddress.BaseLayerMemory 68) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank255
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 256 uses its actual native placement. -/
theorem placement256 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 256 = logical 256 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 256) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[256]'(by decide) = (256, (GKRAddress.BaseLayerMemory 69)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 256 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 69) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 69)) = (GKRAddress.BaseLayerMemory 69) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank256
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 257 uses its actual native placement. -/
theorem placement257 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 257 = logical 257 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 257) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[257]'(by decide) = (257, (GKRAddress.BaseLayerWitness 151)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 257 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 151) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 151)) = (GKRAddress.BaseLayerWitness 151) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank257
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 258 uses its actual native placement. -/
theorem placement258 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 258 = logical 258 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 258) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[258]'(by decide) = (258, (GKRAddress.BaseLayerMemory 72)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 258 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 72) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 72)) = (GKRAddress.BaseLayerMemory 72) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank258
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 259 uses its actual native placement. -/
theorem placement259 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 259 = logical 259 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 259) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[259]'(by decide) = (259, (GKRAddress.BaseLayerMemory 73)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 259 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 73) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 73)) = (GKRAddress.BaseLayerMemory 73) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank259
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 260 uses its actual native placement. -/
theorem placement260 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 260 = logical 260 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 260) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[260]'(by decide) = (260, (GKRAddress.BaseLayerWitness 152)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 260 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 152) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 152)) = (GKRAddress.BaseLayerWitness 152) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank260
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 261 uses its actual native placement. -/
theorem placement261 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 261 = logical 261 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 261) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[261]'(by decide) = (261, (GKRAddress.BaseLayerMemory 76)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 261 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 76) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 76)) = (GKRAddress.BaseLayerMemory 76) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank261
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 262 uses its actual native placement. -/
theorem placement262 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 262 = logical 262 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 262) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[262]'(by decide) = (262, (GKRAddress.BaseLayerMemory 77)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 262 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 77) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 77)) = (GKRAddress.BaseLayerMemory 77) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank262
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 263 uses its actual native placement. -/
theorem placement263 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 263 = logical 263 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 263) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[263]'(by decide) = (263, (GKRAddress.BaseLayerWitness 153)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 263 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 153) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 153)) = (GKRAddress.BaseLayerWitness 153) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank263
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Public placements cover each column in this batch. -/
theorem placements010 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    ∀ index ∈ [240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263],
      (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement240 physical logical agreement) (cons_placements (placement241 physical logical agreement) (cons_placements (placement242 physical logical agreement) (cons_placements (placement243 physical logical agreement) (cons_placements (placement244 physical logical agreement) (cons_placements (placement245 physical logical agreement) (cons_placements (placement246 physical logical agreement) (cons_placements (placement247 physical logical agreement) (cons_placements (placement248 physical logical agreement) (cons_placements (placement249 physical logical agreement) (cons_placements (placement250 physical logical agreement) (cons_placements (placement251 physical logical agreement) (cons_placements (placement252 physical logical agreement) (cons_placements (placement253 physical logical agreement) (cons_placements (placement254 physical logical agreement) (cons_placements (placement255 physical logical agreement) (cons_placements (placement256 physical logical agreement) (cons_placements (placement257 physical logical agreement) (cons_placements (placement258 physical logical agreement) (cons_placements (placement259 physical logical agreement) (cons_placements (placement260 physical logical agreement) (cons_placements (placement261 physical logical agreement) (cons_placements (placement262 physical logical agreement) (cons_placements (placement263 physical logical agreement) (by intro index member; cases member)))))))))))))))))))))))))
end Airbender.Compiler.NativeBindings.Bigint
