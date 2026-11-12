module
public import Proven.Compiler.NativeBridge
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
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[216]'(by decide) =
      (216, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 216)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 217 uses its actual native placement. -/
theorem placement217 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 217 = logical 217 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 217) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[217]'(by decide) =
      (217, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 217)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 218 uses its actual native placement. -/
theorem placement218 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 218 = logical 218 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 218) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[218]'(by decide) =
      (218, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 218)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 219 uses its actual native placement. -/
theorem placement219 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 219 = logical 219 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 219) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[219]'(by decide) =
      (219, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 219)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 220 uses its actual native placement. -/
theorem placement220 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 220 = logical 220 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 220) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[220]'(by decide) =
      (220, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 220)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 221 uses its actual native placement. -/
theorem placement221 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 221 = logical 221 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 221) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[221]'(by decide) =
      (221, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 221)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 222 uses its actual native placement. -/
theorem placement222 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 222 = logical 222 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 222) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[222]'(by decide) =
      (222, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 222)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 223 uses its actual native placement. -/
theorem placement223 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 223 = logical 223 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 223) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[223]'(by decide) =
      (223, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 223)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 224 uses its actual native placement. -/
theorem placement224 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 224 = logical 224 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 224) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[224]'(by decide) =
      (224, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 224)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 225 uses its actual native placement. -/
theorem placement225 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 225 = logical 225 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 225) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[225]'(by decide) =
      (225, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 225)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 226 uses its actual native placement. -/
theorem placement226 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 226 = logical 226 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 226) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[226]'(by decide) =
      (226, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 226)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 227 uses its actual native placement. -/
theorem placement227 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 227 = logical 227 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 227) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[227]'(by decide) =
      (227, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 227)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 228 uses its actual native placement. -/
theorem placement228 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 228 = logical 228 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 228) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[228]'(by decide) =
      (228, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 228)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 229 uses its actual native placement. -/
theorem placement229 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 229 = logical 229 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 229) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[229]'(by decide) =
      (229, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 229)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 230 uses its actual native placement. -/
theorem placement230 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 230 = logical 230 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 230) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[230]'(by decide) =
      (230, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 230)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 231 uses its actual native placement. -/
theorem placement231 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 231 = logical 231 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 231) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[231]'(by decide) =
      (231, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 231)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 232 uses its actual native placement. -/
theorem placement232 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 232 = logical 232 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 232) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[232]'(by decide) =
      (232, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 232)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 233 uses its actual native placement. -/
theorem placement233 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 233 = logical 233 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 233) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[233]'(by decide) =
      (233, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 233)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 234 uses its actual native placement. -/
theorem placement234 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 234 = logical 234 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 234) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[234]'(by decide) =
      (234, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 234)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 235 uses its actual native placement. -/
theorem placement235 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 235 = logical 235 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 235) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[235]'(by decide) =
      (235, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 235)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 236 uses its actual native placement. -/
theorem placement236 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 236 = logical 236 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 236) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[236]'(by decide) =
      (236, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 236)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 237 uses its actual native placement. -/
theorem placement237 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 237 = logical 237 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 237) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[237]'(by decide) =
      (237, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 237)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 238 uses its actual native placement. -/
theorem placement238 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 238 = logical 238 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 238) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[238]'(by decide) =
      (238, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 238)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 239 uses its actual native placement. -/
theorem placement239 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 239 = logical 239 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 239) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[239]'(by decide) =
      (239, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 239)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Public placements cover each column in this batch. -/
theorem placements009 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    ∀ index ∈ [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239],
      (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement216 physical logical agreement) (cons_placements (placement217 physical logical agreement) (cons_placements (placement218 physical logical agreement) (cons_placements (placement219 physical logical agreement) (cons_placements (placement220 physical logical agreement) (cons_placements (placement221 physical logical agreement) (cons_placements (placement222 physical logical agreement) (cons_placements (placement223 physical logical agreement) (cons_placements (placement224 physical logical agreement) (cons_placements (placement225 physical logical agreement) (cons_placements (placement226 physical logical agreement) (cons_placements (placement227 physical logical agreement) (cons_placements (placement228 physical logical agreement) (cons_placements (placement229 physical logical agreement) (cons_placements (placement230 physical logical agreement) (cons_placements (placement231 physical logical agreement) (cons_placements (placement232 physical logical agreement) (cons_placements (placement233 physical logical agreement) (cons_placements (placement234 physical logical agreement) (cons_placements (placement235 physical logical agreement) (cons_placements (placement236 physical logical agreement) (cons_placements (placement237 physical logical agreement) (cons_placements (placement238 physical logical agreement) (cons_placements (placement239 physical logical agreement) (by intro index member; cases member)))))))))))))))))))))))))
end Airbender.Compiler.NativeBindings.Bigint
