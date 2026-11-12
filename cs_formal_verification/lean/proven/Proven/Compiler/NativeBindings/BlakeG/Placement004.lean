module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.BlakeG
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeGCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.BlakeG
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- Logical column 96 uses its actual native placement. -/
theorem placement96 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeG.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get 96 = logical 96 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries) (i := 96) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries[96]'(by decide) =
      (96, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement 96)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 97 uses its actual native placement. -/
theorem placement97 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeG.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get 97 = logical 97 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries) (i := 97) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries[97]'(by decide) =
      (97, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement 97)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 98 uses its actual native placement. -/
theorem placement98 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeG.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get 98 = logical 98 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries) (i := 98) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries[98]'(by decide) =
      (98, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement 98)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 99 uses its actual native placement. -/
theorem placement99 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeG.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get 99 = logical 99 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries) (i := 99) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries[99]'(by decide) =
      (99, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement 99)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 100 uses its actual native placement. -/
theorem placement100 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeG.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get 100 = logical 100 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries) (i := 100) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries[100]'(by decide) =
      (100, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement 100)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 101 uses its actual native placement. -/
theorem placement101 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeG.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get 101 = logical 101 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries) (i := 101) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries[101]'(by decide) =
      (101, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement 101)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 102 uses its actual native placement. -/
theorem placement102 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeG.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get 102 = logical 102 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries) (i := 102) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries[102]'(by decide) =
      (102, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement 102)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 103 uses its actual native placement. -/
theorem placement103 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeG.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get 103 = logical 103 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries) (i := 103) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries[103]'(by decide) =
      (103, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement 103)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 104 uses its actual native placement. -/
theorem placement104 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeG.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get 104 = logical 104 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries) (i := 104) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries[104]'(by decide) =
      (104, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement 104)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 105 uses its actual native placement. -/
theorem placement105 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeG.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get 105 = logical 105 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries) (i := 105) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries[105]'(by decide) =
      (105, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement 105)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 106 uses its actual native placement. -/
theorem placement106 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeG.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get 106 = logical 106 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries) (i := 106) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries[106]'(by decide) =
      (106, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement 106)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 107 uses its actual native placement. -/
theorem placement107 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeG.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get 107 = logical 107 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries) (i := 107) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries[107]'(by decide) =
      (107, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement 107)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 108 uses its actual native placement. -/
theorem placement108 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeG.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get 108 = logical 108 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries) (i := 108) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries[108]'(by decide) =
      (108, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement 108)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 109 uses its actual native placement. -/
theorem placement109 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeG.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get 109 = logical 109 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries) (i := 109) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries[109]'(by decide) =
      (109, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement 109)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 110 uses its actual native placement. -/
theorem placement110 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeG.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get 110 = logical 110 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries) (i := 110) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries[110]'(by decide) =
      (110, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement 110)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 111 uses its actual native placement. -/
theorem placement111 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeG.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get 111 = logical 111 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries) (i := 111) (by decide)
  have binding : (Airbender.Compiler.Captures.BlakeG.imported.circuit).placement_data.entries[111]'(by decide) =
      (111, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement 111)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Public placements cover each column in this batch. -/
theorem placements004 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeG.imported.circuit physical logical) :
    ∀ index ∈ [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111],
      (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement96 physical logical agreement) (cons_placements (placement97 physical logical agreement) (cons_placements (placement98 physical logical agreement) (cons_placements (placement99 physical logical agreement) (cons_placements (placement100 physical logical agreement) (cons_placements (placement101 physical logical agreement) (cons_placements (placement102 physical logical agreement) (cons_placements (placement103 physical logical agreement) (cons_placements (placement104 physical logical agreement) (cons_placements (placement105 physical logical agreement) (cons_placements (placement106 physical logical agreement) (cons_placements (placement107 physical logical agreement) (cons_placements (placement108 physical logical agreement) (cons_placements (placement109 physical logical agreement) (cons_placements (placement110 physical logical agreement) (cons_placements (placement111 physical logical agreement) (by intro index member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.BlakeG
