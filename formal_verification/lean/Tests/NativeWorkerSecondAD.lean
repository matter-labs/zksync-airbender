import Airbender.Review.Trace.Families.ReducedMachine.WorkerSecondADTheorems
import Tests.NativeWorkerCB

namespace Airbender.Tests.NativeWorkerSecondAD
open Airbender.NativeWorkerSecondAD Airbender.Verification Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.ReducedMachine.NativeMemoryBoundary
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure reference vector, not an accepted native witness. -/
theorem wrap_rotation_vector :
    (0xFFFF0001 : BitVec 32)+(0x00010003 : BitVec 32)+(0xFFFFFFFF : BitVec 32) = 3 ∧
      (((0x12345678 : BitVec 32) ^^^ (3 : BitVec 32)).rotateRight 8) = (0x7B123456 : BitVec 32) := by decide +kernel

theorem rotated_chunk_maximum : (15+16*7+128*511 : Nat) = 65535 := by decide +kernel

theorem byte_rotation_reference (b0 b1 b2 b3 : BitVec 8) :
    BitVec.append (BitVec.append b0 b3) (BitVec.append b2 b1) =
      (BitVec.append (BitVec.append b3 b2) (BitVec.append b1 b0)).rotateRight 8 :=
  Airbender.NativeWorkerSecondADProofs.rotate8 b0 b1 b2 b3

/-- Old complete LOCAL BODY only; its zero-pointer aliases stay visible. -/
theorem full_local_second_ad : LocalEffects Airbender.Blake2Worker.PositiveRow.assignment :=
  native_worker_second_ad Airbender.Blake2Worker.PositiveRowProofs.body

theorem zero_a_sums (column : Fin 4) (limb : Fin 2) :
    sumLimb Airbender.Blake2Worker.PositiveRow.assignment column limb = 0 := by
  fin_cases column <;> fin_cases limb <;>
    simp [sumLimb,bInput,carry,Airbender.NativeWorkerFirstG.sumLimb,Airbender.NativeWorkerFirstG.carry,
      Airbender.NativeWorkerInitial.observed,Airbender.NativeWorkerInitial.initialColumns,
      Airbender.NativeWorkerSchedule.selected,Airbender.Blake2Worker.PositiveRow.assignment]

theorem zero_d_outputs (column : Fin 4) : dAfter Airbender.Blake2Worker.PositiveRow.assignment column = 0 := by
  fin_cases column <;> decide +kernel

theorem all_carry_bits {w : Nat → F} (effects : LocalEffects w) :
    ∀ column : Fin 4, ∀ slot : Fin 4, (carryBit w column slot).val ≤ 1 := effects.carries

theorem all_limb_bounds {w : Nat → F} (effects : LocalEffects w) :
    ∀ column : Fin 4, ∀ limb : Fin 2, (sumLimb w column limb).val < 65536 ∧ (dInput w column limb).val < 65536 := effects.bounds

theorem all_b_input_bounds {w : Nat → F} (effects : Airbender.NativeWorkerSecondAD.RowEffects w) :
    ∀ column : Fin 4, ∀ limb : Fin 2, (bInput w column limb).val < 65536 := effects.bBounds

theorem encoded_carry_bounds {w : Nat → F} (effects : Airbender.NativeWorkerSecondAD.RowEffects w) :
    ∀ column : Fin 4, ∀ limb : Fin 2, (carry w column limb).val ≤ 3 := effects.carries

theorem all_second_a_additions {w : Nat → F} (effects : Airbender.NativeWorkerSecondAD.RowEffects w) :
    ∀ column : Fin 4, Airbender.NativeWorkerFirstG.pack (sumLimb w column 0) (sumLimb w column 1) =
      Airbender.NativeWorkerAddition.aAfter w column + Airbender.NativeWorkerCB.bAfter w column +
        Airbender.NativeWorkerAddition.messageWord w ⟨2*column.val+1,by have := column.isLt; omega⟩ := effects.added

theorem all_chained_d_rotations {w : Nat → F} (effects : Airbender.NativeWorkerSecondAD.RowEffects w) :
    ∀ column : Fin 4, dAfter w column = (Airbender.NativeWorkerFirstG.dAfter w column ^^^
      Airbender.NativeWorkerFirstG.pack (sumLimb w column 0) (sumLimb w column 1)).rotateRight 8 := effects.chained

theorem weighted_messages_retained {w : Nat → F} (effects : Airbender.NativeWorkerSecondAD.RowEffects w) :
    ∀ word : Fin 16, ∀ limb : Fin 2,
      (Airbender.NativeWorkerSchedule.selected w word limb).val = Airbender.NativeWorkerAddition.selectedNatural w word limb ∧
        Airbender.NativeWorkerAddition.selectedNatural w word limb < 655360 := effects.prior.prior.selected

private def corrupt (column : Nat) : F := if column = 302 then 1 else Airbender.Blake2Worker.PositiveRow.assignment column

theorem corrupt_d_output_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment corrupt) (constraints Airbender.Blake2Worker.Fixed.table) := by
  intro holds
  have bad := (native_worker_second_ad holds).rotated 0
  exact (by decide +kernel : ¬ (dAfter corrupt 0 =
    (Airbender.NativeWorkerFirstG.pack (dInput corrupt 0 0) (dInput corrupt 0 1) ^^^
      Airbender.NativeWorkerFirstG.pack (sumLimb corrupt 0 0) (sumLimb corrupt 0 1)).rotateRight 8)) bad

theorem inactive_requests_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeWorkerCB.inactive_requests_retained
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
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerSecondAD.RowEffects w :=
  native_counted_worker_second_ad publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeWorkerSecondAD
