import Airbender.Review.Trace.Families.ReducedMachine.WorkerCBTheorems
import Tests.NativeWorkerAddition

namespace Airbender.Tests.NativeWorkerCB
open Airbender.NativeWorkerCB Airbender.Verification Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.ReducedMachine.NativeMemoryBoundary
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure nonzero wrap/XOR/rotation vector, not an accepted native witness. -/
theorem wrap_rotation_vector :
    (0xFFFF0001 : BitVec 32)+(0x00010003 : BitVec 32) = 4 ∧
      (((0x12345678 : BitVec 32) ^^^ (4 : BitVec 32)).rotateRight 12) = (0x67C12345 : BitVec 32) := by decide +kernel

theorem triple_maximum : (7+8*511+4096*15 : Nat) = 65535 := by decide +kernel

theorem chunk_rotation_reference (l0 h0 : BitVec 3) (l1 h1 : BitVec 9) (l2 h2 : BitVec 4) :
    BitVec.append (BitVec.append (BitVec.append l1 l0) h2) (BitVec.append (BitVec.append h1 h0) l2) =
    (BitVec.append (BitVec.append h2 (BitVec.append h1 h0)) (BitVec.append l2 (BitVec.append l1 l0))).rotateRight 12 :=
  Airbender.NativeWorkerCBProofs.rotate12 l0 h0 l1 h1 l2 h2

/-- Reuse the complete old LOCAL BODY; pointer aliases remain visible. -/
theorem full_local_cb : LocalEffects Airbender.Blake2Worker.PositiveRow.assignment :=
  native_worker_first_cb Airbender.Blake2Worker.PositiveRowProofs.body

theorem zero_c_sums (column : Fin 4) (limb : Fin 2) :
    cLimb Airbender.Blake2Worker.PositiveRow.assignment column limb = 0 := by
  fin_cases column <;> fin_cases limb <;>
    simp [cLimb,cInput,dLimb,dByte,carry,Airbender.NativeWorkerInitial.observed,
      Airbender.NativeWorkerInitial.initialColumns,Airbender.Blake2Worker.PositiveRow.assignment]

theorem zero_b_outputs (column : Fin 4) : bAfter Airbender.Blake2Worker.PositiveRow.assignment column = 0 := by
  fin_cases column <;> decide +kernel

theorem all_carry_bits {w : Nat → F} (effects : LocalEffects w) :
    ∀ column : Fin 4, ∀ limb : Fin 2, (carry w column limb).val ≤ 1 := effects.carries

theorem all_limb_bounds {w : Nat → F} (effects : LocalEffects w) :
    ∀ column : Fin 4, ∀ limb : Fin 2, (cLimb w column limb).val < 65536 ∧ (bInput w column limb).val < 65536 := effects.bounds

theorem all_b_rotations {w : Nat → F} (effects : LocalEffects w) :
    ∀ column : Fin 4, bAfter w column =
      (Airbender.NativeWorkerFirstG.pack (bInput w column 0) (bInput w column 1) ^^^
        Airbender.NativeWorkerFirstG.pack (cLimb w column 0) (cLimb w column 1)).rotateRight 12 := effects.rotated

theorem all_c_additions {w : Nat → F} (effects : Airbender.NativeWorkerCB.RowEffects w) :
    ∀ column : Fin 4, Airbender.NativeWorkerFirstG.pack (cLimb w column 0) (cLimb w column 1) =
      Airbender.NativeWorkerAddition.preGWord w ⟨8+column.val,by have := column.isLt; omega⟩ +
        Airbender.NativeWorkerFirstG.dAfter w column := effects.added

theorem weighted_messages_retained {w : Nat → F} (effects : Airbender.NativeWorkerCB.RowEffects w) :
    ∀ word : Fin 16, ∀ limb : Fin 2,
      (Airbender.NativeWorkerSchedule.selected w word limb).val = Airbender.NativeWorkerAddition.selectedNatural w word limb ∧
        Airbender.NativeWorkerAddition.selectedNatural w word limb < 655360 := effects.prior.selected

private def corrupt (column : Nat) : F := if column = 288 then 1 else Airbender.Blake2Worker.PositiveRow.assignment column

theorem corrupt_b_output_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment corrupt) (constraints Airbender.Blake2Worker.Fixed.table) := by
  intro holds
  have bad := (native_worker_first_cb holds).rotated 0
  exact (by decide +kernel : ¬ (bAfter corrupt 0 =
    (Airbender.NativeWorkerFirstG.pack (bInput corrupt 0 0) (bInput corrupt 0 1) ^^^
      Airbender.NativeWorkerFirstG.pack (cLimb corrupt 0 0) (cLimb corrupt 0 1)).rotateRight 12)) bad

theorem inactive_requests_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeWorkerAddition.inactive_requests_retained
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
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerCB.RowEffects w :=
  native_counted_worker_first_cb publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeWorkerCB
