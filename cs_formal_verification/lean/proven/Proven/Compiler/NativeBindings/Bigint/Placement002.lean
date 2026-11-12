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

/-- Logical column 48 uses its actual native placement. -/
theorem placement48 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 48 = logical 48 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 48) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[48]'(by decide) =
      (48, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 48)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 49 uses its actual native placement. -/
theorem placement49 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 49 = logical 49 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 49) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[49]'(by decide) =
      (49, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 49)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 50 uses its actual native placement. -/
theorem placement50 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 50 = logical 50 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 50) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[50]'(by decide) =
      (50, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 50)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 51 uses its actual native placement. -/
theorem placement51 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 51 = logical 51 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 51) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[51]'(by decide) =
      (51, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 51)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 52 uses its actual native placement. -/
theorem placement52 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 52 = logical 52 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 52) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[52]'(by decide) =
      (52, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 52)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 53 uses its actual native placement. -/
theorem placement53 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 53 = logical 53 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 53) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[53]'(by decide) =
      (53, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 53)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 54 uses its actual native placement. -/
theorem placement54 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 54 = logical 54 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 54) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[54]'(by decide) =
      (54, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 54)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 55 uses its actual native placement. -/
theorem placement55 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 55 = logical 55 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 55) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[55]'(by decide) =
      (55, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 55)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 56 uses its actual native placement. -/
theorem placement56 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 56 = logical 56 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 56) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[56]'(by decide) =
      (56, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 56)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 57 uses its actual native placement. -/
theorem placement57 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 57 = logical 57 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 57) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[57]'(by decide) =
      (57, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 57)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 58 uses its actual native placement. -/
theorem placement58 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 58 = logical 58 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 58) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[58]'(by decide) =
      (58, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 58)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 59 uses its actual native placement. -/
theorem placement59 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 59 = logical 59 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 59) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[59]'(by decide) =
      (59, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 59)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 60 uses its actual native placement. -/
theorem placement60 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 60 = logical 60 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 60) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[60]'(by decide) =
      (60, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 60)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 61 uses its actual native placement. -/
theorem placement61 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 61 = logical 61 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 61) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[61]'(by decide) =
      (61, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 61)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 62 uses its actual native placement. -/
theorem placement62 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 62 = logical 62 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 62) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[62]'(by decide) =
      (62, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 62)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 63 uses its actual native placement. -/
theorem placement63 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 63 = logical 63 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 63) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[63]'(by decide) =
      (63, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 63)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 64 uses its actual native placement. -/
theorem placement64 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 64 = logical 64 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 64) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[64]'(by decide) =
      (64, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 64)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 65 uses its actual native placement. -/
theorem placement65 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 65 = logical 65 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 65) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[65]'(by decide) =
      (65, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 65)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 66 uses its actual native placement. -/
theorem placement66 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 66 = logical 66 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 66) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[66]'(by decide) =
      (66, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 66)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 67 uses its actual native placement. -/
theorem placement67 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 67 = logical 67 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 67) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[67]'(by decide) =
      (67, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 67)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 68 uses its actual native placement. -/
theorem placement68 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 68 = logical 68 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 68) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[68]'(by decide) =
      (68, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 68)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 69 uses its actual native placement. -/
theorem placement69 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 69 = logical 69 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 69) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[69]'(by decide) =
      (69, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 69)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 70 uses its actual native placement. -/
theorem placement70 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 70 = logical 70 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 70) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[70]'(by decide) =
      (70, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 70)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 71 uses its actual native placement. -/
theorem placement71 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 71 = logical 71 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 71) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[71]'(by decide) =
      (71, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 71)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Public placements cover each column in this batch. -/
theorem placements002 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    ∀ index ∈ [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71],
      (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement48 physical logical agreement) (cons_placements (placement49 physical logical agreement) (cons_placements (placement50 physical logical agreement) (cons_placements (placement51 physical logical agreement) (cons_placements (placement52 physical logical agreement) (cons_placements (placement53 physical logical agreement) (cons_placements (placement54 physical logical agreement) (cons_placements (placement55 physical logical agreement) (cons_placements (placement56 physical logical agreement) (cons_placements (placement57 physical logical agreement) (cons_placements (placement58 physical logical agreement) (cons_placements (placement59 physical logical agreement) (cons_placements (placement60 physical logical agreement) (cons_placements (placement61 physical logical agreement) (cons_placements (placement62 physical logical agreement) (cons_placements (placement63 physical logical agreement) (cons_placements (placement64 physical logical agreement) (cons_placements (placement65 physical logical agreement) (cons_placements (placement66 physical logical agreement) (cons_placements (placement67 physical logical agreement) (cons_placements (placement68 physical logical agreement) (cons_placements (placement69 physical logical agreement) (cons_placements (placement70 physical logical agreement) (cons_placements (placement71 physical logical agreement) (by intro index member; cases member)))))))))))))))))))))))))
end Airbender.Compiler.NativeBindings.Bigint
