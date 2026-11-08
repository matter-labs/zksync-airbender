import Airbender.Review.Trace.Families.ReducedMachine.WorkerTransitionTheorems
import Tests.NativeWorkerFinalization

namespace Airbender.Tests.NativeWorkerTransition
open Airbender.NativeWorkerTransition Airbender.Verification Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.ReducedMachine.NativeMemoryBoundary
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure independent reference data, not accepted native/global witnesses. -/
private def sample (control : Nat) : Input :=
  ⟨123,control,
    (fun word limb => Airbender.NativeWorkerInitial.limbOf ((0x11223344*(word.val+1))%2^32) limb),
    (fun word limb => Airbender.NativeWorkerInitial.limbOf ((0x01020304*(word.val+1))%2^32) limb),
    (fun word limb => Airbender.NativeWorkerInitial.limbOf ((0x11111111*(word.val+1))%2^32) limb)⟩

theorem independent_column_multiple : column (sample 24) 0 = #v[0x6DB5A35B,0xA4F69A17,0x6CB48B04,0x9F0E29D9] := by decide +kernel

theorem independent_diagonal_multiple : diagonal (sample 24) 0 = #v[0x62BCF3F9,0xC8888686,0x8F0896E9,0x36D8AC6E] := by decide +kernel

theorem independent_diagonal_destinations :
    #v[extendedWord (sample 24) 0,extendedWord (sample 24) 5,
      extendedWord (sample 24) 10,extendedWord (sample 24) 15] = #v[0x62BCF3F9,0xC8888686,0x8F0896E9,0x36D8AC6E] := by decide +kernel

theorem independent_round9_first : (transition (sample 4096)).state 0 = (0x335C11E9 : BitVec 32) := by decide +kernel

theorem independent_round9_last : (transition (sample 4096)).state 7 = (0x16B95E94 : BitVec 32) := by decide +kernel

theorem independent_reduce_final : (transition (sample 513)).state 0 = (0xD995CC95 : BitVec 32) := by decide +kernel

theorem multiple_mask_copy (word : Fin 8) :
    (transition (sample 24)).state word = Airbender.NativeWorkerFirstG.pack
      ((sample 24).state word 0) ((sample 24).state word 1) := by
  have h : performFinal (sample 24) = false := by decide +kernel
  simp [transition,stateWord,h]

theorem zero_mask_messages (word : Fin 16) : selectedWord (sample 0) word = 0 := by
  simp [selectedWord,selectedLimb,bit,sample]

theorem configured_compression_initial :
    #v[initialWord (sample 12) 0,initialWord (sample 12) 12,initialWord (sample 12) 14] =
      #v[(0x6B08E647 : BitVec 32),0x510E523F,0xE07C2654] := by decide +kernel

theorem compression_sides :
    #v[Airbender.NativeWorkerFirstG.pack (inputLimb (sample 12) 0 0) (inputLimb (sample 12) 0 1),
      Airbender.NativeWorkerFirstG.pack (inputLimb (sample 14) 0 0) (inputLimb (sample 14) 0 1),
      Airbender.NativeWorkerFirstG.pack (inputLimb (sample 12) 8 0) (inputLimb (sample 12) 8 1),
      Airbender.NativeWorkerFirstG.pack (inputLimb (sample 14) 8 0) (inputLimb (sample 14) 8 1)] =
      #v[(0x11223344 : BitVec 32),0x11111111,0x11111111,0x11223344] := by decide +kernel

private def wide : Input := { sample 8184 with message := fun _ limb => if limb.val = 0 then 65535 else 0 }
theorem wide_selected_carry : selectedLimb wide 0 0 = 655350 ∧ selectedWord wide 0 = (655350 : BitVec 32) := by decide +kernel

theorem next_controls :
    (fun j : Fin 5 => (transition (sample (#v[0,24,4096,513,8191][j]))).controlHigh) =
      #v[0,48,0,1025,8183].get := by
  funext j
  fin_cases j <;> decide +kernel

theorem both_control_reads (w : Nat → F) :
    (keyValue w 42 false)[(0 : Fin 2)] = (readInput w).controlLow ∧
    (keyValue w 42 false)[(1 : Fin 2)].val = (readInput w).controlHigh :=
  Airbender.NativeWorkerTransitionProofs.read_control w

theorem all_read_inputs (w : Nat → F) (word : Fin 16) (limb : Fin 2) :
    (keyValue w ⟨26+word.val,by have := word.isLt; omega⟩ false)[limb] = (readInput w).message word limb :=
  Airbender.NativeWorkerTransitionProofs.read_message w word limb

theorem actual_output_values (w : Nat → F) : observed w =
    ⟨Airbender.NativeWorkerFinalization.writeWord w,Airbender.NativeWorkerExtendedOutput.writeWord w,(w 136).val,(w 137).val⟩ :=
  Airbender.NativeWorkerTransitionProofs.output_values w

theorem all_state_results {w : Nat → F} (e : RowEffects w) :
    (observed w).state = (transition (readInput w)).state := congrArg Output.state e.result

theorem all_extended_results {w : Nat → F} (e : RowEffects w) :
    (observed w).extended = (transition (readInput w)).extended := congrArg Output.extended e.result

theorem all_control_results {w : Nat → F} (e : RowEffects w) :
    (observed w).controlLow = 0 ∧ (observed w).controlHigh = Airbender.NativeWorkerSchedule.nextHigh (w 135).val := by
  rw [e.result]
  exact ⟨rfl,rfl⟩

theorem old_full_local_body : Airbender.NativeWorkerFinalization.LocalEffects Airbender.Blake2Worker.PositiveRow.assignment :=
  Airbender.Tests.NativeWorkerFinalization.full_local_finalization

theorem inactive_requests_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeWorkerFinalization.inactive_requests_retained

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
  native_counted_worker_transition publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeWorkerTransition
