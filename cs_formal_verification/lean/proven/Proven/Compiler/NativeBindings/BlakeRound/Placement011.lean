module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.BlakeRound
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.BlakeRound
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- Logical column 264 uses its actual native placement. -/
theorem placement264 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 264 = logical 264 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 264) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[264]'(by decide) =
      (264, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 264)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 265 uses its actual native placement. -/
theorem placement265 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 265 = logical 265 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 265) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[265]'(by decide) =
      (265, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 265)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 266 uses its actual native placement. -/
theorem placement266 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 266 = logical 266 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 266) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[266]'(by decide) =
      (266, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 266)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 267 uses its actual native placement. -/
theorem placement267 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 267 = logical 267 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 267) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[267]'(by decide) =
      (267, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 267)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 268 uses its actual native placement. -/
theorem placement268 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 268 = logical 268 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 268) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[268]'(by decide) =
      (268, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 268)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 269 uses its actual native placement. -/
theorem placement269 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 269 = logical 269 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 269) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[269]'(by decide) =
      (269, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 269)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 270 uses its actual native placement. -/
theorem placement270 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 270 = logical 270 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 270) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[270]'(by decide) =
      (270, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 270)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 271 uses its actual native placement. -/
theorem placement271 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 271 = logical 271 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 271) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[271]'(by decide) =
      (271, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 271)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 272 uses its actual native placement. -/
theorem placement272 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 272 = logical 272 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 272) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[272]'(by decide) =
      (272, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 272)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 273 uses its actual native placement. -/
theorem placement273 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 273 = logical 273 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 273) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[273]'(by decide) =
      (273, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 273)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 274 uses its actual native placement. -/
theorem placement274 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 274 = logical 274 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 274) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[274]'(by decide) =
      (274, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 274)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 275 uses its actual native placement. -/
theorem placement275 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 275 = logical 275 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 275) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[275]'(by decide) =
      (275, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 275)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 276 uses its actual native placement. -/
theorem placement276 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 276 = logical 276 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 276) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[276]'(by decide) =
      (276, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 276)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 277 uses its actual native placement. -/
theorem placement277 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 277 = logical 277 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 277) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[277]'(by decide) =
      (277, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 277)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 278 uses its actual native placement. -/
theorem placement278 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 278 = logical 278 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 278) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[278]'(by decide) =
      (278, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 278)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 279 uses its actual native placement. -/
theorem placement279 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 279 = logical 279 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 279) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[279]'(by decide) =
      (279, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 279)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 280 uses its actual native placement. -/
theorem placement280 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 280 = logical 280 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 280) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[280]'(by decide) =
      (280, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 280)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 281 uses its actual native placement. -/
theorem placement281 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 281 = logical 281 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 281) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[281]'(by decide) =
      (281, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 281)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 282 uses its actual native placement. -/
theorem placement282 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 282 = logical 282 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 282) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[282]'(by decide) =
      (282, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 282)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 283 uses its actual native placement. -/
theorem placement283 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 283 = logical 283 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 283) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[283]'(by decide) =
      (283, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 283)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 284 uses its actual native placement. -/
theorem placement284 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 284 = logical 284 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 284) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[284]'(by decide) =
      (284, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 284)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 285 uses its actual native placement. -/
theorem placement285 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 285 = logical 285 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 285) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[285]'(by decide) =
      (285, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 285)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 286 uses its actual native placement. -/
theorem placement286 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 286 = logical 286 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 286) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[286]'(by decide) =
      (286, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 286)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 287 uses its actual native placement. -/
theorem placement287 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 287 = logical 287 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 287) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[287]'(by decide) =
      (287, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 287)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Public placements cover each column in this batch. -/
theorem placements011 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    ∀ index ∈ [264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287],
      (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement264 physical logical agreement) (cons_placements (placement265 physical logical agreement) (cons_placements (placement266 physical logical agreement) (cons_placements (placement267 physical logical agreement) (cons_placements (placement268 physical logical agreement) (cons_placements (placement269 physical logical agreement) (cons_placements (placement270 physical logical agreement) (cons_placements (placement271 physical logical agreement) (cons_placements (placement272 physical logical agreement) (cons_placements (placement273 physical logical agreement) (cons_placements (placement274 physical logical agreement) (cons_placements (placement275 physical logical agreement) (cons_placements (placement276 physical logical agreement) (cons_placements (placement277 physical logical agreement) (cons_placements (placement278 physical logical agreement) (cons_placements (placement279 physical logical agreement) (cons_placements (placement280 physical logical agreement) (cons_placements (placement281 physical logical agreement) (cons_placements (placement282 physical logical agreement) (cons_placements (placement283 physical logical agreement) (cons_placements (placement284 physical logical agreement) (cons_placements (placement285 physical logical agreement) (cons_placements (placement286 physical logical agreement) (cons_placements (placement287 physical logical agreement) (by intro index member; cases member)))))))))))))))))))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
