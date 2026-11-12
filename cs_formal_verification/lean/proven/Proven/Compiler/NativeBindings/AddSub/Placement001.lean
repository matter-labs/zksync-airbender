module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.AddSub
public import Proven.GKRProtocol.CleanArithmeticNative.AddSubCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.AddSub
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- Logical column 24 uses its actual native placement. -/
theorem placement24 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 24 = logical 24 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 24) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[24]'(by decide) =
      (24, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 24)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 25 uses its actual native placement. -/
theorem placement25 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 25 = logical 25 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 25) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[25]'(by decide) =
      (25, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 25)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 26 uses its actual native placement. -/
theorem placement26 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 26 = logical 26 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 26) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[26]'(by decide) =
      (26, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 26)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 27 uses its actual native placement. -/
theorem placement27 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 27 = logical 27 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 27) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[27]'(by decide) =
      (27, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 27)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 28 uses its actual native placement. -/
theorem placement28 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 28 = logical 28 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 28) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[28]'(by decide) =
      (28, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 28)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 29 uses its actual native placement. -/
theorem placement29 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 29 = logical 29 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 29) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[29]'(by decide) =
      (29, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 29)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 30 uses its actual native placement. -/
theorem placement30 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 30 = logical 30 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 30) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[30]'(by decide) =
      (30, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 30)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 31 uses its actual native placement. -/
theorem placement31 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 31 = logical 31 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 31) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[31]'(by decide) =
      (31, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 31)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 32 uses its actual native placement. -/
theorem placement32 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 32 = logical 32 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 32) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[32]'(by decide) =
      (32, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 32)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 33 uses its actual native placement. -/
theorem placement33 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 33 = logical 33 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 33) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[33]'(by decide) =
      (33, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 33)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 34 uses its actual native placement. -/
theorem placement34 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 34 = logical 34 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 34) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[34]'(by decide) =
      (34, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 34)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 35 uses its actual native placement. -/
theorem placement35 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 35 = logical 35 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 35) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[35]'(by decide) =
      (35, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 35)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 36 uses its actual native placement. -/
theorem placement36 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 36 = logical 36 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 36) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[36]'(by decide) =
      (36, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 36)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 37 uses its actual native placement. -/
theorem placement37 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 37 = logical 37 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 37) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[37]'(by decide) =
      (37, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 37)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 38 uses its actual native placement. -/
theorem placement38 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 38 = logical 38 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 38) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[38]'(by decide) =
      (38, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 38)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 39 uses its actual native placement. -/
theorem placement39 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 39 = logical 39 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 39) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[39]'(by decide) =
      (39, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 39)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 40 uses its actual native placement. -/
theorem placement40 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 40 = logical 40 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 40) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[40]'(by decide) =
      (40, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 40)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 41 uses its actual native placement. -/
theorem placement41 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 41 = logical 41 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 41) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[41]'(by decide) =
      (41, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 41)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 42 uses its actual native placement. -/
theorem placement42 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 42 = logical 42 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 42) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[42]'(by decide) =
      (42, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 42)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 43 uses its actual native placement. -/
theorem placement43 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 43 = logical 43 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 43) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[43]'(by decide) =
      (43, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 43)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 44 uses its actual native placement. -/
theorem placement44 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 44 = logical 44 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 44) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[44]'(by decide) =
      (44, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 44)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 45 uses its actual native placement. -/
theorem placement45 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 45 = logical 45 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 45) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[45]'(by decide) =
      (45, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 45)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 46 uses its actual native placement. -/
theorem placement46 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 46 = logical 46 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 46) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[46]'(by decide) =
      (46, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 46)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 47 uses its actual native placement. -/
theorem placement47 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get 47 = logical 47 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries) (i := 47) (by decide)
  have binding : (Airbender.Compiler.Captures.AddSub.imported.circuit).placement_data.entries[47]'(by decide) =
      (47, Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement 47)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Public placements cover each column in this batch. -/
theorem placements001 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.AddSub.imported.circuit physical logical) :
    ∀ index ∈ [24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47],
      (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement24 physical logical agreement) (cons_placements (placement25 physical logical agreement) (cons_placements (placement26 physical logical agreement) (cons_placements (placement27 physical logical agreement) (cons_placements (placement28 physical logical agreement) (cons_placements (placement29 physical logical agreement) (cons_placements (placement30 physical logical agreement) (cons_placements (placement31 physical logical agreement) (cons_placements (placement32 physical logical agreement) (cons_placements (placement33 physical logical agreement) (cons_placements (placement34 physical logical agreement) (cons_placements (placement35 physical logical agreement) (cons_placements (placement36 physical logical agreement) (cons_placements (placement37 physical logical agreement) (cons_placements (placement38 physical logical agreement) (cons_placements (placement39 physical logical agreement) (cons_placements (placement40 physical logical agreement) (cons_placements (placement41 physical logical agreement) (cons_placements (placement42 physical logical agreement) (cons_placements (placement43 physical logical agreement) (cons_placements (placement44 physical logical agreement) (cons_placements (placement45 physical logical agreement) (cons_placements (placement46 physical logical agreement) (cons_placements (placement47 physical logical agreement) (by intro index member; cases member)))))))))))))))))))))))))
end Airbender.Compiler.NativeBindings.AddSub
