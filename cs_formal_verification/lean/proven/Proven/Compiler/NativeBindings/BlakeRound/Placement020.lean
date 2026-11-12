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

/-- Logical column 480 uses its actual native placement. -/
theorem placement480 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 480 = logical 480 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 480) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[480]'(by decide) =
      (480, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 480)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 481 uses its actual native placement. -/
theorem placement481 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 481 = logical 481 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 481) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[481]'(by decide) =
      (481, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 481)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 482 uses its actual native placement. -/
theorem placement482 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 482 = logical 482 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 482) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[482]'(by decide) =
      (482, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 482)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 483 uses its actual native placement. -/
theorem placement483 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 483 = logical 483 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 483) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[483]'(by decide) =
      (483, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 483)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 484 uses its actual native placement. -/
theorem placement484 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 484 = logical 484 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 484) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[484]'(by decide) =
      (484, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 484)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 485 uses its actual native placement. -/
theorem placement485 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 485 = logical 485 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 485) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[485]'(by decide) =
      (485, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 485)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 486 uses its actual native placement. -/
theorem placement486 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 486 = logical 486 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 486) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[486]'(by decide) =
      (486, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 486)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 487 uses its actual native placement. -/
theorem placement487 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 487 = logical 487 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 487) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[487]'(by decide) =
      (487, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 487)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 488 uses its actual native placement. -/
theorem placement488 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 488 = logical 488 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 488) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[488]'(by decide) =
      (488, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 488)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 489 uses its actual native placement. -/
theorem placement489 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 489 = logical 489 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 489) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[489]'(by decide) =
      (489, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 489)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 490 uses its actual native placement. -/
theorem placement490 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 490 = logical 490 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 490) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[490]'(by decide) =
      (490, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 490)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 491 uses its actual native placement. -/
theorem placement491 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 491 = logical 491 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 491) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[491]'(by decide) =
      (491, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 491)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 492 uses its actual native placement. -/
theorem placement492 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 492 = logical 492 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 492) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[492]'(by decide) =
      (492, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 492)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 493 uses its actual native placement. -/
theorem placement493 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 493 = logical 493 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 493) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[493]'(by decide) =
      (493, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 493)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 494 uses its actual native placement. -/
theorem placement494 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 494 = logical 494 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 494) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[494]'(by decide) =
      (494, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 494)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 495 uses its actual native placement. -/
theorem placement495 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 495 = logical 495 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 495) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[495]'(by decide) =
      (495, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 495)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 496 uses its actual native placement. -/
theorem placement496 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 496 = logical 496 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 496) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[496]'(by decide) =
      (496, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 496)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 497 uses its actual native placement. -/
theorem placement497 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 497 = logical 497 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 497) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[497]'(by decide) =
      (497, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 497)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 498 uses its actual native placement. -/
theorem placement498 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 498 = logical 498 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 498) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[498]'(by decide) =
      (498, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 498)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 499 uses its actual native placement. -/
theorem placement499 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 499 = logical 499 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 499) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[499]'(by decide) =
      (499, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 499)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 500 uses its actual native placement. -/
theorem placement500 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 500 = logical 500 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 500) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[500]'(by decide) =
      (500, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 500)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 501 uses its actual native placement. -/
theorem placement501 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 501 = logical 501 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 501) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[501]'(by decide) =
      (501, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 501)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 502 uses its actual native placement. -/
theorem placement502 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 502 = logical 502 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 502) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[502]'(by decide) =
      (502, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 502)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 503 uses its actual native placement. -/
theorem placement503 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 503 = logical 503 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 503) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[503]'(by decide) =
      (503, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 503)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Public placements cover each column in this batch. -/
theorem placements020 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    ∀ index ∈ [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503],
      (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement480 physical logical agreement) (cons_placements (placement481 physical logical agreement) (cons_placements (placement482 physical logical agreement) (cons_placements (placement483 physical logical agreement) (cons_placements (placement484 physical logical agreement) (cons_placements (placement485 physical logical agreement) (cons_placements (placement486 physical logical agreement) (cons_placements (placement487 physical logical agreement) (cons_placements (placement488 physical logical agreement) (cons_placements (placement489 physical logical agreement) (cons_placements (placement490 physical logical agreement) (cons_placements (placement491 physical logical agreement) (cons_placements (placement492 physical logical agreement) (cons_placements (placement493 physical logical agreement) (cons_placements (placement494 physical logical agreement) (cons_placements (placement495 physical logical agreement) (cons_placements (placement496 physical logical agreement) (cons_placements (placement497 physical logical agreement) (cons_placements (placement498 physical logical agreement) (cons_placements (placement499 physical logical agreement) (cons_placements (placement500 physical logical agreement) (cons_placements (placement501 physical logical agreement) (cons_placements (placement502 physical logical agreement) (cons_placements (placement503 physical logical agreement) (by intro index member; cases member)))))))))))))))))))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
