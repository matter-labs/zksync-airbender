import Airbender.Review.Trace.Families.ReducedMachine.WorkerExtendedOutputTheorems
import Tests.NativeWorkerDiagonalG

namespace Airbender.Tests.NativeWorkerExtendedOutput
open Airbender.NativeWorkerExtendedOutput Airbender.Verification Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.ReducedMachine.NativeMemoryBoundary
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure call-site coordinates; no native acceptance is supplied. -/
theorem diagonal_destinations :
    (fun c : Fin 4 => (destination 0 c).val) = #v[0,5,10,15].get ∧
    (fun c : Fin 4 => (destination 1 c).val) = #v[1,6,11,12].get ∧
    (fun c : Fin 4 => (destination 2 c).val) = #v[2,7,8,13].get ∧
    (fun c : Fin 4 => (destination 3 c).val) = #v[3,4,9,14].get := by
  refine ⟨?_,?_,?_,?_⟩ <;> funext c <;> fin_cases c <;> rfl

theorem all_output_positions (word : Fin 16) : destination (diagonalOf word) (componentOf word) = word :=
  Airbender.NativeWorkerExtendedOutputProofs.destination_inverse word

theorem actual_write_columns :
    (fun c : Fin 4 => writeLimb (fun n => (n : F)) (destination 0 c) 0) = #v[38,58,78,98].get := by
  funext c
  fin_cases c <;> rfl

theorem b_canonical_maximum : (511+512*127 : Nat) = 65535 := by decide +kernel

/-- Complete old LOCAL BODY only; its zero-pointer aliases remain visible. -/
theorem full_local_output : ∀ word : Fin 16,
    writeWord Airbender.Blake2Worker.PositiveRow.assignment word =
      (Airbender.NativeWorkerDiagonalG.diagonalResult Airbender.Blake2Worker.PositiveRow.assignment (diagonalOf word))[componentOf word] :=
  native_worker_extended_output Airbender.Blake2Worker.PositiveRowProofs.body

theorem zero_written_words (word : Fin 16) : writeWord Airbender.Blake2Worker.PositiveRow.assignment word = 0 := by
  fin_cases word <;> decide +kernel

theorem all_actual_limbs {w : Nat → F} (effects : Airbender.NativeWorkerExtendedOutput.RowEffects w) :
    ∀ d c : Fin 4, ∀ limb : Fin 2, writeLimb w (destination d c) limb = resultLimb w d c limb := effects.limbs

theorem all_actual_words {w : Nat → F} (effects : Airbender.NativeWorkerExtendedOutput.RowEffects w) :
    ∀ word : Fin 16, writeWord w word =
      (Airbender.NativeWorkerDiagonalG.diagonalResult w (diagonalOf word))[componentOf word] := effects.written

theorem prior_g_retained {w : Nat → F} (effects : Airbender.NativeWorkerExtendedOutput.RowEffects w) :
    Airbender.NativeWorkerDiagonalG.RowEffects w := effects.prior

theorem weighted_messages_retained {w : Nat → F} (effects : Airbender.NativeWorkerExtendedOutput.RowEffects w) :
    ∀ word : Fin 16, ∀ limb : Fin 2, (Airbender.NativeWorkerSchedule.selected w word limb).val < 655360 := by
  intro word limb
  have h := Airbender.Tests.NativeWorkerDiagonalG.weighted_messages_retained effects.prior word limb
  rw [h.1]
  exact h.2

private def corrupt (column index : Nat) : F := if index = column then 1 else Airbender.Blake2Worker.PositiveRow.assignment index

theorem corrupt_a_write_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (corrupt 38)) (constraints Airbender.Blake2Worker.Fixed.table) := by
  intro holds
  have bad := native_worker_extended_writes holds 0 0 0
  exact (by decide +kernel : ¬ (writeLimb (corrupt 38) (destination 0 0) 0 = resultLimb (corrupt 38) 0 0 0)) bad

theorem corrupt_b_write_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (corrupt 54)) (constraints Airbender.Blake2Worker.Fixed.table) := by
  intro holds
  have bad := native_worker_extended_writes holds 3 1 0
  exact (by decide +kernel : ¬ (writeLimb (corrupt 54) (destination 3 1) 0 = resultLimb (corrupt 54) 3 1 0)) bad

theorem corrupt_c_write_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (corrupt 70)) (constraints Airbender.Blake2Worker.Fixed.table) := by
  intro holds
  have bad := native_worker_extended_writes holds 2 2 0
  exact (by decide +kernel : ¬ (writeLimb (corrupt 70) (destination 2 2) 0 = resultLimb (corrupt 70) 2 2 0)) bad

theorem corrupt_d_write_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (corrupt 86)) (constraints Airbender.Blake2Worker.Fixed.table) := by
  intro holds
  have bad := native_worker_extended_writes holds 1 3 0
  exact (by decide +kernel : ¬ (writeLimb (corrupt 86) (destination 1 3) 0 = resultLimb (corrupt 86) 1 3 0)) bad

theorem inactive_requests_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeWorkerDiagonalG.inactive_requests_retained
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
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerExtendedOutput.RowEffects w :=
  native_counted_worker_extended_output publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeWorkerExtendedOutput
