module
public import Proven.Compiler.NativeBridge
public import Proven.Compiler.NativeBindings.Keccak.PlacementData
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
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[264]'(by decide) = (264, (GKRAddress.BaseLayerWitness 173)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 264 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 173) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 173)) = (GKRAddress.BaseLayerWitness 173) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank264
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Logical column 265 uses its actual native placement. -/
theorem placement265 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 265 = logical 265 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 265) (by decide)
  have captured : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[265]'(by decide) = (265, (GKRAddress.BaseLayerWitness 174)) :=
    entry_of_binding (by decide) placement_entries (by cbv)
  have same := agreement _ included
  rw [captured] at same
  have selected : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 265 = Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 174) := by
    as_aux_lemma => kernel_rfl
  have inverse : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.placement (GKRAddress.BaseLayerWitness 174)) = (GKRAddress.BaseLayerWitness 174) :=
    of_decide_eq_true Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placementInBank265
  exact (congrArg physical ((congrArg Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address selected).trans inverse)).trans same.symm

/-- Public placements cover each column in this batch. -/
theorem placements011 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    ∀ index ∈ [264, 265],
      (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement264 physical logical agreement) (cons_placements (placement265 physical logical agreement) (by intro index member; cases member)))
end Airbender.Compiler.NativeBindings.Keccak
