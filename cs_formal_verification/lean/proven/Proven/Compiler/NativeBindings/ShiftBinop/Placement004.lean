module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.ShiftBinop
public import Proven.GKRProtocol.CleanArithmeticNative.ShiftBinopCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.ShiftBinop
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- Logical column 96 uses its actual native placement. -/
theorem placement96 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical (Verification.environment logical).data).get 96 = logical 96 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.ShiftBinop.imported.circuit).placement_data.entries) (i := 96) (by decide)
  have binding : (Airbender.Compiler.Captures.ShiftBinop.imported.circuit).placement_data.entries[96]'(by decide) =
      (96, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.placement 96)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 97 uses its actual native placement. -/
theorem placement97 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical (Verification.environment logical).data).get 97 = logical 97 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.ShiftBinop.imported.circuit).placement_data.entries) (i := 97) (by decide)
  have binding : (Airbender.Compiler.Captures.ShiftBinop.imported.circuit).placement_data.entries[97]'(by decide) =
      (97, Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.placement 97)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Public placements cover each column in this batch. -/
theorem placements004 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical logical) :
    ∀ index ∈ [96, 97],
      (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement96 physical logical agreement) (cons_placements (placement97 physical logical agreement) (by intro index member; cases member)))
end Airbender.Compiler.NativeBindings.ShiftBinop
