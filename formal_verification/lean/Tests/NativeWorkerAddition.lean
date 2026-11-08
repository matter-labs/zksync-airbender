import Airbender.Review.Trace.Families.ReducedMachine.WorkerAdditionTheorems
import Tests.NativeWorkerFirstG

namespace Airbender.Tests.NativeWorkerAddition
open Airbender.NativeWorkerAddition Airbender.NativeWorkerSchedule Airbender.NativeWorkerInitial
open Airbender.Verification Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.ReducedMachine.NativeMemoryBoundary
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure weighted controls, not accepted native or physical witnesses. -/
theorem all_round_bits_wide :
    (∑ _r : Fin 10, (1 : F)*(65535 : F)).val = 655350 ∧ 65536 ≤ (655350 : Nat) := by
  have h := Airbender.NativeWorkerAdditionProofs.weighted_sum (fun _ => 1) (fun _ => (65535 : F))
    (fun _ => by decide +kernel) (fun _ => by decide +kernel)
  norm_num at h ⊢
  exact h.1

theorem zero_round_bits : (∑ _r : Fin 10, (0 : F)*(65535 : F)).val = 0 := by simp

theorem native_carry_encoding_three : ((1 : F)+2*(1 : F)).val = 3 ∧ ((1 : F)+2*(1 : F)).val ≤ 3 := by
  decide +kernel

theorem wide_limb_addition :
    BitVec.ofNat 32 (65532+65536*65535) = BitVec.ofNat 32 (65535+65536*65535) +
      BitVec.ofNat 32 (65535+65536*65535) + BitVec.ofNat 32 (131070+65536*131070) :=
  Airbender.NativeWorkerAdditionProofs.wide_add _ _ _ _ _ _ _ _ 3 3 (by decide +kernel) (by decide +kernel)

theorem wide_addition_wrap : BitVec.ofNat 32 (65532+65536*65535) = (0xFFFFFFFC : BitVec 32) := by decide +kernel

/-- Wide selected limbs must retain carry into the high half before RV32 reduction. -/
theorem truncating_each_wide_limb_changes_word :
    BitVec.ofNat 32 (65536+65536*0) ≠ Airbender.NativeWorkerFirstG.pack (65536 : F) 0 := by decide +kernel

theorem all_initial_limbs {w : Nat → F} (effects : Airbender.NativeWorkerAddition.RowEffects w) :
    ∀ word : Fin 16, ∀ limb : Fin 2, (observed w word limb).val < 65536 := effects.initial

theorem all_compression_inputs {w : Nat → F} (effects : Airbender.NativeWorkerAddition.RowEffects w) :
    ∀ word : Fin 16, ∀ limb : Fin 2, (input w word limb).val < 65536 := effects.inputs

theorem all_weighted_messages {w : Nat → F} (effects : Airbender.NativeWorkerAddition.RowEffects w) :
    ∀ word : Fin 16, ∀ limb : Fin 2, (selected w word limb).val = selectedNatural w word limb ∧
      selectedNatural w word limb < 655360 := effects.selected

theorem all_actual_carries {w : Nat → F} (effects : Airbender.NativeWorkerAddition.RowEffects w) :
    ∀ column : Fin 4, ∀ limb : Fin 2, (Airbender.NativeWorkerFirstG.carry w column limb).val ≤ 3 := effects.carries

theorem all_wrapping_additions {w : Nat → F} (effects : Airbender.NativeWorkerAddition.RowEffects w) :
    ∀ column : Fin 4, aAfter w column = preGWord w ⟨column.val,by have := column.isLt; omega⟩ +
      preGWord w ⟨4+column.val,by have := column.isLt; omega⟩ +
      messageWord w ⟨2*column.val,by have := column.isLt; omega⟩ := effects.added

theorem exact_d_rotations_retained {w : Nat → F} (effects : Airbender.NativeWorkerAddition.RowEffects w) :
    ∀ column : Fin 4, Airbender.NativeWorkerFirstG.dAfter w column =
      (Airbender.NativeWorkerFirstG.pack (Airbender.NativeWorkerFirstG.dInput w column 0) (Airbender.NativeWorkerFirstG.dInput w column 1) ^^^
        aAfter w column).rotateRight 16 := effects.prior.rotated

theorem inactive_requests_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeWorkerFirstG.inactive_requests_retained
theorem complete_counted {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Airbender.NativeCallerDecoder.Mode)
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : Airbender.NativeCallerDecoder.setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.main.proofs workers) :
    Airbender.NativeMixedReplay.Effects batch workers inputs ∧
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerAddition.RowEffects w :=
  native_counted_worker_first_addition publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeWorkerAddition
