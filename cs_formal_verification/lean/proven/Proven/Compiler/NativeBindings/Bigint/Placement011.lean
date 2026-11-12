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

/-- Logical column 264 uses its actual native placement. -/
theorem placement264 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 264 = logical 264 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 264) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[264]'(by decide) =
      (264, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 264)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 265 uses its actual native placement. -/
theorem placement265 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 265 = logical 265 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 265) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[265]'(by decide) =
      (265, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 265)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 266 uses its actual native placement. -/
theorem placement266 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 266 = logical 266 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 266) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[266]'(by decide) =
      (266, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 266)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 267 uses its actual native placement. -/
theorem placement267 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 267 = logical 267 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 267) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[267]'(by decide) =
      (267, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 267)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 268 uses its actual native placement. -/
theorem placement268 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 268 = logical 268 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 268) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[268]'(by decide) =
      (268, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 268)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 269 uses its actual native placement. -/
theorem placement269 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 269 = logical 269 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 269) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[269]'(by decide) =
      (269, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 269)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 270 uses its actual native placement. -/
theorem placement270 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 270 = logical 270 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 270) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[270]'(by decide) =
      (270, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 270)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 271 uses its actual native placement. -/
theorem placement271 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 271 = logical 271 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 271) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[271]'(by decide) =
      (271, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 271)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 272 uses its actual native placement. -/
theorem placement272 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 272 = logical 272 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 272) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[272]'(by decide) =
      (272, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 272)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 273 uses its actual native placement. -/
theorem placement273 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 273 = logical 273 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 273) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[273]'(by decide) =
      (273, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 273)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 274 uses its actual native placement. -/
theorem placement274 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 274 = logical 274 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 274) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[274]'(by decide) =
      (274, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 274)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 275 uses its actual native placement. -/
theorem placement275 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get 275 = logical 275 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries) (i := 275) (by decide)
  have binding : (Airbender.Compiler.Captures.Bigint.imported.circuit).placement_data.entries[275]'(by decide) =
      (275, Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement 275)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Public placements cover each column in this batch. -/
theorem placements011 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Bigint.imported.circuit physical logical) :
    ∀ index ∈ [264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275],
      (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement264 physical logical agreement) (cons_placements (placement265 physical logical agreement) (cons_placements (placement266 physical logical agreement) (cons_placements (placement267 physical logical agreement) (cons_placements (placement268 physical logical agreement) (cons_placements (placement269 physical logical agreement) (cons_placements (placement270 physical logical agreement) (cons_placements (placement271 physical logical agreement) (cons_placements (placement272 physical logical agreement) (cons_placements (placement273 physical logical agreement) (cons_placements (placement274 physical logical agreement) (cons_placements (placement275 physical logical agreement) (by intro index member; cases member)))))))))))))
end Airbender.Compiler.NativeBindings.Bigint
