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

/-- Logical column 216 uses its actual native placement. -/
theorem placement216 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 216 = logical 216 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 216) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[216]'(by decide) = (216, (GKRAddress.BaseLayerMemory 0)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 216 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 0) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 0)) = (GKRAddress.BaseLayerMemory 0) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank216
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 217 uses its actual native placement. -/
theorem placement217 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 217 = logical 217 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 217) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[217]'(by decide) = (217, (GKRAddress.BaseLayerMemory 1)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 217 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 1) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 1)) = (GKRAddress.BaseLayerMemory 1) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank217
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 218 uses its actual native placement. -/
theorem placement218 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 218 = logical 218 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 218) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[218]'(by decide) = (218, (GKRAddress.BaseLayerWitness 138)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 218 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 138) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 138)) = (GKRAddress.BaseLayerWitness 138) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank218
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 219 uses its actual native placement. -/
theorem placement219 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 219 = logical 219 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 219) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[219]'(by decide) = (219, (GKRAddress.BaseLayerMemory 4)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 219 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 4) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 4)) = (GKRAddress.BaseLayerMemory 4) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank219
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 220 uses its actual native placement. -/
theorem placement220 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 220 = logical 220 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 220) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[220]'(by decide) = (220, (GKRAddress.BaseLayerMemory 5)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 220 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 5) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 5)) = (GKRAddress.BaseLayerMemory 5) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank220
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 221 uses its actual native placement. -/
theorem placement221 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 221 = logical 221 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 221) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[221]'(by decide) = (221, (GKRAddress.BaseLayerWitness 139)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 221 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 139) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 139)) = (GKRAddress.BaseLayerWitness 139) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank221
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 222 uses its actual native placement. -/
theorem placement222 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 222 = logical 222 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 222) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[222]'(by decide) = (222, (GKRAddress.BaseLayerMemory 10)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 222 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 10) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 10)) = (GKRAddress.BaseLayerMemory 10) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank222
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 223 uses its actual native placement. -/
theorem placement223 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 223 = logical 223 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 223) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[223]'(by decide) = (223, (GKRAddress.BaseLayerMemory 11)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 223 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 11) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 11)) = (GKRAddress.BaseLayerMemory 11) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank223
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 224 uses its actual native placement. -/
theorem placement224 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 224 = logical 224 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 224) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[224]'(by decide) = (224, (GKRAddress.BaseLayerWitness 140)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 224 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 140) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 140)) = (GKRAddress.BaseLayerWitness 140) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank224
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 225 uses its actual native placement. -/
theorem placement225 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 225 = logical 225 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 225) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[225]'(by decide) = (225, (GKRAddress.BaseLayerMemory 16)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 225 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 16) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 16)) = (GKRAddress.BaseLayerMemory 16) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank225
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 226 uses its actual native placement. -/
theorem placement226 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 226 = logical 226 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 226) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[226]'(by decide) = (226, (GKRAddress.BaseLayerMemory 17)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 226 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 17) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 17)) = (GKRAddress.BaseLayerMemory 17) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank226
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 227 uses its actual native placement. -/
theorem placement227 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 227 = logical 227 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 227) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[227]'(by decide) = (227, (GKRAddress.BaseLayerWitness 141)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 227 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 141) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 141)) = (GKRAddress.BaseLayerWitness 141) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank227
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 228 uses its actual native placement. -/
theorem placement228 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 228 = logical 228 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 228) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[228]'(by decide) = (228, (GKRAddress.BaseLayerMemory 22)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 228 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 22) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 22)) = (GKRAddress.BaseLayerMemory 22) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank228
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 229 uses its actual native placement. -/
theorem placement229 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 229 = logical 229 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 229) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[229]'(by decide) = (229, (GKRAddress.BaseLayerMemory 23)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 229 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 23) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 23)) = (GKRAddress.BaseLayerMemory 23) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank229
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 230 uses its actual native placement. -/
theorem placement230 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 230 = logical 230 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 230) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[230]'(by decide) = (230, (GKRAddress.BaseLayerWitness 142)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 230 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 142) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 142)) = (GKRAddress.BaseLayerWitness 142) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank230
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 231 uses its actual native placement. -/
theorem placement231 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 231 = logical 231 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 231) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[231]'(by decide) = (231, (GKRAddress.BaseLayerMemory 28)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 231 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 28) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 28)) = (GKRAddress.BaseLayerMemory 28) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank231
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 232 uses its actual native placement. -/
theorem placement232 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 232 = logical 232 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 232) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[232]'(by decide) = (232, (GKRAddress.BaseLayerMemory 29)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 232 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 29) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 29)) = (GKRAddress.BaseLayerMemory 29) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank232
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 233 uses its actual native placement. -/
theorem placement233 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 233 = logical 233 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 233) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[233]'(by decide) = (233, (GKRAddress.BaseLayerWitness 143)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 233 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 143) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 143)) = (GKRAddress.BaseLayerWitness 143) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank233
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 234 uses its actual native placement. -/
theorem placement234 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 234 = logical 234 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 234) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[234]'(by decide) = (234, (GKRAddress.BaseLayerMemory 34)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 234 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 34) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 34)) = (GKRAddress.BaseLayerMemory 34) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank234
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 235 uses its actual native placement. -/
theorem placement235 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 235 = logical 235 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 235) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[235]'(by decide) = (235, (GKRAddress.BaseLayerMemory 35)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 235 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 35) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 35)) = (GKRAddress.BaseLayerMemory 35) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank235
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 236 uses its actual native placement. -/
theorem placement236 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 236 = logical 236 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 236) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[236]'(by decide) = (236, (GKRAddress.BaseLayerWitness 144)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 236 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 144) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 144)) = (GKRAddress.BaseLayerWitness 144) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank236
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 237 uses its actual native placement. -/
theorem placement237 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 237 = logical 237 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 237) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[237]'(by decide) = (237, (GKRAddress.BaseLayerMemory 40)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 237 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 40) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 40)) = (GKRAddress.BaseLayerMemory 40) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank237
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 238 uses its actual native placement. -/
theorem placement238 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 238 = logical 238 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 238) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[238]'(by decide) = (238, (GKRAddress.BaseLayerMemory 41)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 238 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 41) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerMemory 41)) = (GKRAddress.BaseLayerMemory 41) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank238
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 239 uses its actual native placement. -/
theorem placement239 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 239 = logical 239 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 239) (by decide)
  have captured : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[239]'(by decide) = (239, (GKRAddress.BaseLayerWitness 145)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 239 = Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 145) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.placement (GKRAddress.BaseLayerWitness 145)) = (GKRAddress.BaseLayerWitness 145) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placementInBank239
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Public placements cover each column in this batch. -/
theorem placements009 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    ∀ index ∈ [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239],
      (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement216 physical logical agreement) (cons_placements (placement217 physical logical agreement) (cons_placements (placement218 physical logical agreement) (cons_placements (placement219 physical logical agreement) (cons_placements (placement220 physical logical agreement) (cons_placements (placement221 physical logical agreement) (cons_placements (placement222 physical logical agreement) (cons_placements (placement223 physical logical agreement) (cons_placements (placement224 physical logical agreement) (cons_placements (placement225 physical logical agreement) (cons_placements (placement226 physical logical agreement) (cons_placements (placement227 physical logical agreement) (cons_placements (placement228 physical logical agreement) (cons_placements (placement229 physical logical agreement) (cons_placements (placement230 physical logical agreement) (cons_placements (placement231 physical logical agreement) (cons_placements (placement232 physical logical agreement) (cons_placements (placement233 physical logical agreement) (cons_placements (placement234 physical logical agreement) (cons_placements (placement235 physical logical agreement) (cons_placements (placement236 physical logical agreement) (cons_placements (placement237 physical logical agreement) (cons_placements (placement238 physical logical agreement) (cons_placements (placement239 physical logical agreement) (by intro index member; cases member)))))))))))))))))))))))))
end Airbender.Compiler.NativeBindings.Bigint
