module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.WordMemory
public import Proven.GKRProtocol.CleanArithmeticNative.WordMemoryCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.WordMemory
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- Logical column 48 uses its actual native placement. -/
theorem placement48 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.WordMemory.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical (Verification.environment logical).data).get 48 = logical 48 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.WordMemory.imported.circuit).placement_data.entries) (i := 48) (by decide)
  have binding : (Airbender.Compiler.Captures.WordMemory.imported.circuit).placement_data.entries[48]'(by decide) =
      (48, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.placement 48)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 49 uses its actual native placement. -/
theorem placement49 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.WordMemory.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical (Verification.environment logical).data).get 49 = logical 49 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.WordMemory.imported.circuit).placement_data.entries) (i := 49) (by decide)
  have binding : (Airbender.Compiler.Captures.WordMemory.imported.circuit).placement_data.entries[49]'(by decide) =
      (49, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.placement 49)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 50 uses its actual native placement. -/
theorem placement50 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.WordMemory.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical (Verification.environment logical).data).get 50 = logical 50 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.WordMemory.imported.circuit).placement_data.entries) (i := 50) (by decide)
  have binding : (Airbender.Compiler.Captures.WordMemory.imported.circuit).placement_data.entries[50]'(by decide) =
      (50, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.placement 50)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 51 uses its actual native placement. -/
theorem placement51 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.WordMemory.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical (Verification.environment logical).data).get 51 = logical 51 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.WordMemory.imported.circuit).placement_data.entries) (i := 51) (by decide)
  have binding : (Airbender.Compiler.Captures.WordMemory.imported.circuit).placement_data.entries[51]'(by decide) =
      (51, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.placement 51)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Public placements cover each column in this batch. -/
theorem placements002 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.WordMemory.imported.circuit physical logical) :
    ∀ index ∈ [48, 49, 50, 51],
      (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement48 physical logical agreement) (cons_placements (placement49 physical logical agreement) (cons_placements (placement50 physical logical agreement) (cons_placements (placement51 physical logical agreement) (by intro index member; cases member)))))
end Airbender.Compiler.NativeBindings.WordMemory
