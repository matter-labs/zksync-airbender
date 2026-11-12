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

/-- Logical column 576 uses its actual native placement. -/
theorem placement576 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 576 = logical 576 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 576) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[576]'(by decide) =
      (576, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 576)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 577 uses its actual native placement. -/
theorem placement577 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 577 = logical 577 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 577) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[577]'(by decide) =
      (577, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 577)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 578 uses its actual native placement. -/
theorem placement578 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 578 = logical 578 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 578) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[578]'(by decide) =
      (578, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 578)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 579 uses its actual native placement. -/
theorem placement579 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 579 = logical 579 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 579) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[579]'(by decide) =
      (579, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 579)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 580 uses its actual native placement. -/
theorem placement580 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 580 = logical 580 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 580) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[580]'(by decide) =
      (580, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 580)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 581 uses its actual native placement. -/
theorem placement581 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 581 = logical 581 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 581) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[581]'(by decide) =
      (581, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 581)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 582 uses its actual native placement. -/
theorem placement582 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 582 = logical 582 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 582) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[582]'(by decide) =
      (582, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 582)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 583 uses its actual native placement. -/
theorem placement583 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 583 = logical 583 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 583) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[583]'(by decide) =
      (583, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 583)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 584 uses its actual native placement. -/
theorem placement584 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 584 = logical 584 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 584) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[584]'(by decide) =
      (584, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 584)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 585 uses its actual native placement. -/
theorem placement585 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 585 = logical 585 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 585) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[585]'(by decide) =
      (585, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 585)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 586 uses its actual native placement. -/
theorem placement586 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 586 = logical 586 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 586) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[586]'(by decide) =
      (586, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 586)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 587 uses its actual native placement. -/
theorem placement587 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 587 = logical 587 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 587) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[587]'(by decide) =
      (587, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 587)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 588 uses its actual native placement. -/
theorem placement588 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 588 = logical 588 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 588) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[588]'(by decide) =
      (588, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 588)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 589 uses its actual native placement. -/
theorem placement589 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 589 = logical 589 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 589) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[589]'(by decide) =
      (589, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 589)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 590 uses its actual native placement. -/
theorem placement590 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 590 = logical 590 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 590) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[590]'(by decide) =
      (590, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 590)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 591 uses its actual native placement. -/
theorem placement591 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 591 = logical 591 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 591) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[591]'(by decide) =
      (591, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 591)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 592 uses its actual native placement. -/
theorem placement592 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 592 = logical 592 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 592) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[592]'(by decide) =
      (592, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 592)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 593 uses its actual native placement. -/
theorem placement593 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 593 = logical 593 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 593) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[593]'(by decide) =
      (593, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 593)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 594 uses its actual native placement. -/
theorem placement594 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 594 = logical 594 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 594) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[594]'(by decide) =
      (594, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 594)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 595 uses its actual native placement. -/
theorem placement595 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 595 = logical 595 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 595) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[595]'(by decide) =
      (595, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 595)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 596 uses its actual native placement. -/
theorem placement596 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 596 = logical 596 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 596) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[596]'(by decide) =
      (596, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 596)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 597 uses its actual native placement. -/
theorem placement597 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 597 = logical 597 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 597) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[597]'(by decide) =
      (597, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 597)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 598 uses its actual native placement. -/
theorem placement598 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 598 = logical 598 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 598) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[598]'(by decide) =
      (598, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 598)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 599 uses its actual native placement. -/
theorem placement599 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 599 = logical 599 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 599) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[599]'(by decide) =
      (599, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 599)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Public placements cover each column in this batch. -/
theorem placements024 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    ∀ index ∈ [576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599],
      (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement576 physical logical agreement) (cons_placements (placement577 physical logical agreement) (cons_placements (placement578 physical logical agreement) (cons_placements (placement579 physical logical agreement) (cons_placements (placement580 physical logical agreement) (cons_placements (placement581 physical logical agreement) (cons_placements (placement582 physical logical agreement) (cons_placements (placement583 physical logical agreement) (cons_placements (placement584 physical logical agreement) (cons_placements (placement585 physical logical agreement) (cons_placements (placement586 physical logical agreement) (cons_placements (placement587 physical logical agreement) (cons_placements (placement588 physical logical agreement) (cons_placements (placement589 physical logical agreement) (cons_placements (placement590 physical logical agreement) (cons_placements (placement591 physical logical agreement) (cons_placements (placement592 physical logical agreement) (cons_placements (placement593 physical logical agreement) (cons_placements (placement594 physical logical agreement) (cons_placements (placement595 physical logical agreement) (cons_placements (placement596 physical logical agreement) (cons_placements (placement597 physical logical agreement) (cons_placements (placement598 physical logical agreement) (cons_placements (placement599 physical logical agreement) (by intro index member; cases member)))))))))))))))))))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
