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

/-- Logical column 0 uses its actual native placement. -/
theorem placement0 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 0 = logical 0 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 0) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[0]'(by decide) =
      (0, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 0)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 1 uses its actual native placement. -/
theorem placement1 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 1 = logical 1 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 1) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[1]'(by decide) =
      (1, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 1)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 2 uses its actual native placement. -/
theorem placement2 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 2 = logical 2 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 2) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[2]'(by decide) =
      (2, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 2)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 3 uses its actual native placement. -/
theorem placement3 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 3 = logical 3 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 3) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[3]'(by decide) =
      (3, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 3)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 4 uses its actual native placement. -/
theorem placement4 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 4 = logical 4 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 4) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[4]'(by decide) =
      (4, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 4)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 5 uses its actual native placement. -/
theorem placement5 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 5 = logical 5 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 5) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[5]'(by decide) =
      (5, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 5)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 6 uses its actual native placement. -/
theorem placement6 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 6 = logical 6 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 6) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[6]'(by decide) =
      (6, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 6)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 7 uses its actual native placement. -/
theorem placement7 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 7 = logical 7 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 7) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[7]'(by decide) =
      (7, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 7)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 8 uses its actual native placement. -/
theorem placement8 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 8 = logical 8 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 8) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[8]'(by decide) =
      (8, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 8)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 9 uses its actual native placement. -/
theorem placement9 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 9 = logical 9 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 9) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[9]'(by decide) =
      (9, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 9)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 10 uses its actual native placement. -/
theorem placement10 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 10 = logical 10 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 10) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[10]'(by decide) =
      (10, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 10)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 11 uses its actual native placement. -/
theorem placement11 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 11 = logical 11 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 11) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[11]'(by decide) =
      (11, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 11)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 12 uses its actual native placement. -/
theorem placement12 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 12 = logical 12 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 12) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[12]'(by decide) =
      (12, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 12)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 13 uses its actual native placement. -/
theorem placement13 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 13 = logical 13 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 13) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[13]'(by decide) =
      (13, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 13)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 14 uses its actual native placement. -/
theorem placement14 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 14 = logical 14 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 14) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[14]'(by decide) =
      (14, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 14)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 15 uses its actual native placement. -/
theorem placement15 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 15 = logical 15 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 15) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[15]'(by decide) =
      (15, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 15)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 16 uses its actual native placement. -/
theorem placement16 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 16 = logical 16 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 16) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[16]'(by decide) =
      (16, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 16)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 17 uses its actual native placement. -/
theorem placement17 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 17 = logical 17 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 17) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[17]'(by decide) =
      (17, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 17)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 18 uses its actual native placement. -/
theorem placement18 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 18 = logical 18 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 18) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[18]'(by decide) =
      (18, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 18)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 19 uses its actual native placement. -/
theorem placement19 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 19 = logical 19 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 19) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[19]'(by decide) =
      (19, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 19)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 20 uses its actual native placement. -/
theorem placement20 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 20 = logical 20 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 20) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[20]'(by decide) =
      (20, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 20)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 21 uses its actual native placement. -/
theorem placement21 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 21 = logical 21 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 21) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[21]'(by decide) =
      (21, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 21)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 22 uses its actual native placement. -/
theorem placement22 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 22 = logical 22 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 22) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[22]'(by decide) =
      (22, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 22)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 23 uses its actual native placement. -/
theorem placement23 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 23 = logical 23 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 23) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[23]'(by decide) =
      (23, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 23)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Public placements cover each column in this batch. -/
theorem placements000 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    ∀ index ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
      (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement0 physical logical agreement) (cons_placements (placement1 physical logical agreement) (cons_placements (placement2 physical logical agreement) (cons_placements (placement3 physical logical agreement) (cons_placements (placement4 physical logical agreement) (cons_placements (placement5 physical logical agreement) (cons_placements (placement6 physical logical agreement) (cons_placements (placement7 physical logical agreement) (cons_placements (placement8 physical logical agreement) (cons_placements (placement9 physical logical agreement) (cons_placements (placement10 physical logical agreement) (cons_placements (placement11 physical logical agreement) (cons_placements (placement12 physical logical agreement) (cons_placements (placement13 physical logical agreement) (cons_placements (placement14 physical logical agreement) (cons_placements (placement15 physical logical agreement) (cons_placements (placement16 physical logical agreement) (cons_placements (placement17 physical logical agreement) (cons_placements (placement18 physical logical agreement) (cons_placements (placement19 physical logical agreement) (cons_placements (placement20 physical logical agreement) (cons_placements (placement21 physical logical agreement) (cons_placements (placement22 physical logical agreement) (cons_placements (placement23 physical logical agreement) (by intro index member; cases member)))))))))))))))))))))))))
end Airbender.Compiler.NativeBindings.Bigint
