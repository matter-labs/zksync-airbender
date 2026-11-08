import Airbender.Review.Trace.Families.ReducedMachine.WorkerScheduleTheorems
import Tests.NativeBlake2PositiveRow
import Tests.NativeMixedWordBounds

namespace Airbender.Tests.NativeWorkerSchedule
open Airbender.NativeWorkerSchedule Airbender.Verification Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.ReducedMachine.NativeMemoryBoundary
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure reference controls, not accepted worker/global witnesses. -/
theorem sigma_rows_permute : ∀ round : Fin 10, (sigma[round]).toList.Perm (List.finRange 16) := by
  decide +kernel

theorem next_control_examples : nextHigh 8 = 16 ∧ nextHigh 4096 = 0 ∧ nextHigh 4097 = 1 ∧ nextHigh 8191 = 8183 := by
  decide +kernel

theorem pure_round_zero_bits : ∀ round : Fin 10,
    8 / 2^(3+round.val) % 2 = if round = 0 then 1 else 0 := by
  decide +kernel

/-- Multiple round bits remain visible; no one-hot inference is made. -/
theorem pure_multiple_round_bits : 24 / 2^3 % 2 = 1 ∧ 24 / 2^4 % 2 = 1 ∧ nextHigh 24 = 48 := by
  decide +kernel

private def withControl (high : Nat) (w : Nat → F) (column : Nat) : F :=
  if column = 135 then high else w column

theorem left_compression_reference (w : Nat → F) :
    input (withControl 4 w) 0 0 = w 4 ∧ input (withControl 4 w) 8 0 = w 102 := by
  have four : (4 : F).val = 4 := by decide +kernel
  simp [input,inputBit,withControl,message,state,four]

theorem right_compression_reference (w : Nat → F) :
    input (withControl 6 w) 0 0 = w 102 ∧ input (withControl 6 w) 8 0 = w 4 := by
  have six : (6 : F).val = 6 := by decide +kernel
  simp [input,inputBit,withControl,message,state,six]

/-- Reuse the complete checked LOCAL fixture; zero-pointer aliases remain.
    This is no new compatible source-global/physical witness. -/
theorem full_local_zero_body : RowEffects Airbender.Blake2Worker.PositiveRow.assignment :=
  native_worker_message_schedule Airbender.Blake2Worker.PositiveRowProofs.body

theorem zero_round_mask (slot : Fin 13) : inputBit Airbender.Blake2Worker.PositiveRow.assignment slot = 0 := by
  simp [inputBit,Airbender.Blake2Worker.PositiveRow.assignment]

theorem actual_zero_selection (word : Fin 16) (limb : Fin 2) :
    selected Airbender.Blake2Worker.PositiveRow.assignment word limb = 0 := by
  rw [full_local_zero_body.schedule]
  unfold scheduled
  apply Finset.sum_eq_zero
  intro round _
  rw [zero_round_mask]
  simp

theorem all_control_bits {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    ∀ slot : Fin 13, w (138+slot.val) = (inputBit w slot : F) :=
  (native_worker_message_schedule holds).flags

theorem compression_operands {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    ∀ word : Fin 16, ∀ limb : Fin 2, w (204+2*word.val+limb.val) = input w word limb :=
  (native_worker_message_schedule holds).inputs

theorem actual_message_schedule {setup : Table F (fields 4)} {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) :
    ∀ word : Fin 16, ∀ limb : Fin 2, selected w word limb = scheduled w word limb :=
  (native_worker_message_schedule holds).schedule

theorem inactive_requests_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeMixedWordBounds.inactive_requests_retained

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
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, RowEffects w :=
  native_counted_worker_message_schedule publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeWorkerSchedule
