import Airbender.Proofs.GKRProtocol.ProductNative.UnifiedUncached

namespace Tests.GKRNativeProduct
open Airbender Airbender.Compiler
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def steps : List ProductStep :=
  [.pair (.InnerLayer 1 0) 0 1,
   .copy (.InnerLayer 2 0) (.InnerLayer 1 0),
   .mask (.InnerLayer 3 0) (.InnerLayer 2 0) (.BaseLayerWitness 0)]

theorem follows_product_copies_and_mask :
    ((ProductStep.run steps []).bind (ProductEnvironment.find (.InnerLayer 3 0))) =
      some (.mask (.BaseLayerWitness 0) (.mul (.leaf 0) (.leaf 1))) := by rfl

theorem rejects_missing_copy :
    (ProductStep.run
      [.pair (.InnerLayer 1 0) 0 1,
       .mask (.InnerLayer 3 0) (.InnerLayer 2 0) (.BaseLayerWitness 0)] []).isSome = false := by decide +kernel

theorem rejects_missing_product_input :
    (ProductStep.run
      [.single (.InnerLayer 1 0) 0, .mul (.InnerLayer 2 0) (.InnerLayer 1 0) (.InnerLayer 1 1)] []).isSome = false := by
  decide +kernel

private def payload : LookupPayload := .input (.BaseLayerMemory 0)

theorem rejects_unknown_gate_selector :
    ¬(NativeProductBinding.mk 1 (.single (.InnerLayer 1 0) 0)).Valid [payload]
      [.single (.InnerLayer 1 0) payload] := by intro impossible; exact impossible

theorem rejects_unknown_primitive_selector :
    ¬(NativeProductGate.single (.InnerLayer 1 0) payload).Normalizes [] (.single (.InnerLayer 1 0) 0) := by
  intro checked
  cases checked.2

theorem rejects_wrong_mask_source :
    ¬(NativeProductGate.mask (.InnerLayer 2 0) (.InnerLayer 1 0) (.BaseLayerWitness 0)).Normalizes []
      (.mask (.InnerLayer 2 0) (.InnerLayer 1 0) (.BaseLayerWitness 1)) := by
  intro checked
  cases checked.2.2

/-- Distribution needs the Boolean/idempotence condition stated by the generic
lemma; arbitrary field-valued predicates do not justify it. -/
theorem rejects_non_boolean_mask_distribution :
    maskProduct (2 : Int) (0 * 0) ≠ maskProduct 2 0 * maskProduct 2 0 := by decide +kernel

private def challenges : CacheChallenges Source.BaseField :=
  ⟨0, 0, fun index => if index.val = 1 then 1 else 0⟩

theorem preserves_initialization_ram_space :
    ProductNative.UnifiedUncached.native.leaf8.interpret (RingHom.id _) challenges (fun _ => 0) = 1 := by
  decide +kernel

/-- The second actual set adds 2^(23+2-16)=512 to its high address limb. -/
theorem preserves_initialization_set_high_offset :
    ProductNative.UnifiedUncached.native.leaf9.interpret (RingHom.id _) challenges (fun _ => 0) = 513 := by
  decide +kernel

theorem rejects_exchanged_read_write_outputs :
    ProductNative.UnifiedUncached.native.memoryReadProduct.leaves ≠
      ProductNative.UnifiedUncached.native.memoryWriteProduct.leaves := by decide +kernel

end Tests.GKRNativeProduct
