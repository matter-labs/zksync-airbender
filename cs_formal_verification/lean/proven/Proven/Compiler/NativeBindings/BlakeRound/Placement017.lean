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

/-- Logical column 408 uses its actual native placement. -/
theorem placement408 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 408 = logical 408 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 408) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[408]'(by decide) =
      (408, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 408)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 409 uses its actual native placement. -/
theorem placement409 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 409 = logical 409 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 409) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[409]'(by decide) =
      (409, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 409)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 410 uses its actual native placement. -/
theorem placement410 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 410 = logical 410 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 410) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[410]'(by decide) =
      (410, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 410)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 411 uses its actual native placement. -/
theorem placement411 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 411 = logical 411 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 411) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[411]'(by decide) =
      (411, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 411)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 412 uses its actual native placement. -/
theorem placement412 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 412 = logical 412 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 412) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[412]'(by decide) =
      (412, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 412)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 413 uses its actual native placement. -/
theorem placement413 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 413 = logical 413 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 413) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[413]'(by decide) =
      (413, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 413)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 414 uses its actual native placement. -/
theorem placement414 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 414 = logical 414 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 414) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[414]'(by decide) =
      (414, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 414)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 415 uses its actual native placement. -/
theorem placement415 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 415 = logical 415 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 415) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[415]'(by decide) =
      (415, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 415)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 416 uses its actual native placement. -/
theorem placement416 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 416 = logical 416 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 416) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[416]'(by decide) =
      (416, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 416)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 417 uses its actual native placement. -/
theorem placement417 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 417 = logical 417 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 417) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[417]'(by decide) =
      (417, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 417)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 418 uses its actual native placement. -/
theorem placement418 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 418 = logical 418 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 418) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[418]'(by decide) =
      (418, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 418)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 419 uses its actual native placement. -/
theorem placement419 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 419 = logical 419 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 419) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[419]'(by decide) =
      (419, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 419)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 420 uses its actual native placement. -/
theorem placement420 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 420 = logical 420 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 420) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[420]'(by decide) =
      (420, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 420)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 421 uses its actual native placement. -/
theorem placement421 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 421 = logical 421 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 421) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[421]'(by decide) =
      (421, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 421)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 422 uses its actual native placement. -/
theorem placement422 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 422 = logical 422 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 422) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[422]'(by decide) =
      (422, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 422)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 423 uses its actual native placement. -/
theorem placement423 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 423 = logical 423 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 423) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[423]'(by decide) =
      (423, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 423)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 424 uses its actual native placement. -/
theorem placement424 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 424 = logical 424 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 424) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[424]'(by decide) =
      (424, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 424)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 425 uses its actual native placement. -/
theorem placement425 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 425 = logical 425 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 425) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[425]'(by decide) =
      (425, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 425)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 426 uses its actual native placement. -/
theorem placement426 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 426 = logical 426 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 426) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[426]'(by decide) =
      (426, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 426)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 427 uses its actual native placement. -/
theorem placement427 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 427 = logical 427 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 427) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[427]'(by decide) =
      (427, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 427)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 428 uses its actual native placement. -/
theorem placement428 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 428 = logical 428 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 428) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[428]'(by decide) =
      (428, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 428)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 429 uses its actual native placement. -/
theorem placement429 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 429 = logical 429 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 429) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[429]'(by decide) =
      (429, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 429)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 430 uses its actual native placement. -/
theorem placement430 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 430 = logical 430 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 430) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[430]'(by decide) =
      (430, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 430)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 431 uses its actual native placement. -/
theorem placement431 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 431 = logical 431 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 431) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[431]'(by decide) =
      (431, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 431)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Public placements cover each column in this batch. -/
theorem placements017 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    ∀ index ∈ [408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431],
      (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement408 physical logical agreement) (cons_placements (placement409 physical logical agreement) (cons_placements (placement410 physical logical agreement) (cons_placements (placement411 physical logical agreement) (cons_placements (placement412 physical logical agreement) (cons_placements (placement413 physical logical agreement) (cons_placements (placement414 physical logical agreement) (cons_placements (placement415 physical logical agreement) (cons_placements (placement416 physical logical agreement) (cons_placements (placement417 physical logical agreement) (cons_placements (placement418 physical logical agreement) (cons_placements (placement419 physical logical agreement) (cons_placements (placement420 physical logical agreement) (cons_placements (placement421 physical logical agreement) (cons_placements (placement422 physical logical agreement) (cons_placements (placement423 physical logical agreement) (cons_placements (placement424 physical logical agreement) (cons_placements (placement425 physical logical agreement) (cons_placements (placement426 physical logical agreement) (cons_placements (placement427 physical logical agreement) (cons_placements (placement428 physical logical agreement) (cons_placements (placement429 physical logical agreement) (cons_placements (placement430 physical logical agreement) (cons_placements (placement431 physical logical agreement) (by intro index member; cases member)))))))))))))))))))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
