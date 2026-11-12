module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.Keccak
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.Keccak
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- Logical column 264 uses its actual native placement. -/
theorem placement264 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 264 = logical 264 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 264) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[264]'(by decide) =
      (264, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 264)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 265 uses its actual native placement. -/
theorem placement265 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 265 = logical 265 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 265) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[265]'(by decide) =
      (265, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 265)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Public placements cover each column in this batch. -/
theorem placements011 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    ∀ index ∈ [264, 265],
      (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement264 physical logical agreement) (cons_placements (placement265 physical logical agreement) (by intro index member; cases member)))
end Airbender.Compiler.NativeBindings.Keccak
