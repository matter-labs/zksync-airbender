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

/-- Logical column 744 uses its actual native placement. -/
theorem placement744 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 744 = logical 744 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 744) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[744]'(by decide) =
      (744, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 744)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 745 uses its actual native placement. -/
theorem placement745 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 745 = logical 745 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 745) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[745]'(by decide) =
      (745, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 745)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 746 uses its actual native placement. -/
theorem placement746 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 746 = logical 746 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 746) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[746]'(by decide) =
      (746, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 746)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 747 uses its actual native placement. -/
theorem placement747 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 747 = logical 747 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 747) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[747]'(by decide) =
      (747, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 747)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 748 uses its actual native placement. -/
theorem placement748 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 748 = logical 748 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 748) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[748]'(by decide) =
      (748, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 748)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 749 uses its actual native placement. -/
theorem placement749 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 749 = logical 749 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 749) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[749]'(by decide) =
      (749, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 749)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 750 uses its actual native placement. -/
theorem placement750 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 750 = logical 750 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 750) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[750]'(by decide) =
      (750, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 750)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 751 uses its actual native placement. -/
theorem placement751 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 751 = logical 751 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 751) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[751]'(by decide) =
      (751, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 751)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 752 uses its actual native placement. -/
theorem placement752 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 752 = logical 752 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 752) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[752]'(by decide) =
      (752, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 752)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 753 uses its actual native placement. -/
theorem placement753 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 753 = logical 753 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 753) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[753]'(by decide) =
      (753, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 753)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 754 uses its actual native placement. -/
theorem placement754 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 754 = logical 754 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 754) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[754]'(by decide) =
      (754, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 754)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 755 uses its actual native placement. -/
theorem placement755 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 755 = logical 755 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 755) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[755]'(by decide) =
      (755, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 755)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 756 uses its actual native placement. -/
theorem placement756 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 756 = logical 756 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 756) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[756]'(by decide) =
      (756, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 756)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 757 uses its actual native placement. -/
theorem placement757 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 757 = logical 757 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 757) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[757]'(by decide) =
      (757, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 757)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 758 uses its actual native placement. -/
theorem placement758 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 758 = logical 758 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 758) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[758]'(by decide) =
      (758, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 758)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 759 uses its actual native placement. -/
theorem placement759 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 759 = logical 759 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 759) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[759]'(by decide) =
      (759, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 759)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 760 uses its actual native placement. -/
theorem placement760 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 760 = logical 760 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 760) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[760]'(by decide) =
      (760, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 760)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 761 uses its actual native placement. -/
theorem placement761 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 761 = logical 761 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 761) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[761]'(by decide) =
      (761, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 761)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 762 uses its actual native placement. -/
theorem placement762 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get 762 = logical 762 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries) (i := 762) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeRound.imported.circuit).placement_data.entries[762]'(by decide) =
      (762, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement 762)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Public placements cover each column in this batch. -/
theorem placements031 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    ∀ index ∈ [744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762],
      (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement744 physical logical agreement) (cons_placements (placement745 physical logical agreement) (cons_placements (placement746 physical logical agreement) (cons_placements (placement747 physical logical agreement) (cons_placements (placement748 physical logical agreement) (cons_placements (placement749 physical logical agreement) (cons_placements (placement750 physical logical agreement) (cons_placements (placement751 physical logical agreement) (cons_placements (placement752 physical logical agreement) (cons_placements (placement753 physical logical agreement) (cons_placements (placement754 physical logical agreement) (cons_placements (placement755 physical logical agreement) (cons_placements (placement756 physical logical agreement) (cons_placements (placement757 physical logical agreement) (cons_placements (placement758 physical logical agreement) (cons_placements (placement759 physical logical agreement) (cons_placements (placement760 physical logical agreement) (cons_placements (placement761 physical logical agreement) (cons_placements (placement762 physical logical agreement) (by intro index member; cases member))))))))))))))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
