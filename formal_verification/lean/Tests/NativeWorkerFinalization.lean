import Airbender.Review.Trace.Families.ReducedMachine.WorkerFinalizationTheorems
import Tests.NativeWorkerExtendedOutput

namespace Airbender.Tests.NativeWorkerFinalization
open Airbender.NativeWorkerFinalization Airbender.Verification Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.ReducedMachine.NativeMemoryBoundary
private abbrev F := ZMod mersenne31Modulus
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure reference data; no native BODY or global-history acceptance claimed. -/
private def sample (index : Nat) : F :=
  if index = 4 then 0x5678 else if index = 5 then 0x1234 else
  if index = 38 then 0xBEEF else if index = 39 then 0xDEAD else
  if index = 70 then 0xCDEF else if index = 71 then 0x89AB else 0

theorem nonzero_xor_reference : xorResult sample 0 = (0x45322578 : BitVec 32) := by decide +kernel

private def withControl (value index : Nat) : F :=
  if index = 135 then (value : F) else Airbender.Blake2Worker.PositiveRow.assignment index

theorem control_choices :
    (fun i : Fin 7 => performFinal (withControl (#v[0,4096,512,513,1,8191,24][i]))) =
      #v[false,true,false,true,false,true,false].get := by
  funext i
  fin_cases i <;> decide +kernel

theorem no_onehot_requirement : performFinal (withControl 8191) = true := by decide +kernel

theorem pure_wide_control : performFinal (withControl 65537) = false := by decide +kernel

/-- Old complete LOCAL BODY only; its zero-pointer aliases remain visible. -/
theorem full_local_finalization : LocalEffects Airbender.Blake2Worker.PositiveRow.assignment :=
  native_worker_finalization Airbender.Blake2Worker.PositiveRowProofs.body

theorem full_local_copy (word : Fin 8) :
    writeWord Airbender.Blake2Worker.PositiveRow.assignment word = readWord Airbender.Blake2Worker.PositiveRow.assignment word := by
  have h := full_local_finalization.finalized word
  simpa [performFinal,Airbender.NativeWorkerSchedule.inputBit,Airbender.Blake2Worker.PositiveRow.assignment] using h

theorem zero_local_writes (word : Fin 8) : writeWord Airbender.Blake2Worker.PositiveRow.assignment word = 0 := by
  fin_cases word <;> decide +kernel

theorem actual_port_values (w : Nat → F) (word : Fin 8) (limb : Fin 2) :
    (keyValue w ⟨1+word.val,by have := word.isLt; omega⟩ true)[limb] = writeLimb w word limb :=
  Airbender.NativeWorkerFinalizationProofs.write_value w word limb

theorem selected_copy {w : Nat → F} (effects : LocalEffects w) (disabled : performFinal w = false) (word : Fin 8) :
    writeWord w word = readWord w word := by simpa [disabled] using effects.finalized word

theorem selected_xor {w : Nat → F} (effects : LocalEffects w) (enabled : performFinal w = true) (word : Fin 8) :
    writeWord w word = xorResult w word := by simpa [enabled] using effects.finalized word

theorem all_state_words {w : Nat → F} (effects : Airbender.NativeWorkerFinalization.RowEffects w) :
    ∀ word : Fin 8, writeWord w word = if performFinal w then xorResult w word else readWord w word := effects.finalized

theorem original_extended_results {w : Nat → F} (effects : Airbender.NativeWorkerFinalization.RowEffects w) :
    Airbender.NativeWorkerExtendedOutput.RowEffects w := effects.prior

theorem weighted_messages_retained {w : Nat → F} (effects : Airbender.NativeWorkerFinalization.RowEffects w) :
    ∀ word : Fin 16, ∀ limb : Fin 2, (Airbender.NativeWorkerSchedule.selected w word limb).val < 655360 :=
  Airbender.Tests.NativeWorkerExtendedOutput.weighted_messages_retained effects.prior

private def corrupt (column index : Nat) : F := if index = column then 1 else Airbender.Blake2Worker.PositiveRow.assignment index

theorem corrupt_first_copy_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (corrupt 6)) (constraints Airbender.Blake2Worker.Fixed.table) := by
  intro holds
  have bad := (native_worker_finalization holds).finalized 0
  exact (by decide +kernel : ¬ (writeWord (corrupt 6) 0 =
    if performFinal (corrupt 6) then xorResult (corrupt 6) 0 else readWord (corrupt 6) 0)) bad

theorem corrupt_last_copy_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (corrupt 35)) (constraints Airbender.Blake2Worker.Fixed.table) := by
  intro holds
  have bad := (native_worker_finalization holds).finalized 7
  exact (by decide +kernel : ¬ (writeWord (corrupt 35) 7 =
    if performFinal (corrupt 35) then xorResult (corrupt 35) 7 else readWord (corrupt 35) 7)) bad

theorem corrupt_ac_xor_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (corrupt 633)) (constraints Airbender.Blake2Worker.Fixed.table) := by
  intro holds
  have bad := Airbender.NativeWorkerFinalizationProofs.xor_word holds 0
  change (1 : BitVec 32) = 0 at bad
  exact (by decide +kernel : (1 : BitVec 32) ≠ 0) bad

theorem corrupt_bd_xor_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (corrupt 689)) (constraints Airbender.Blake2Worker.Fixed.table) := by
  intro holds
  have bad := Airbender.NativeWorkerFinalizationProofs.xor_word holds 4
  change (1 : BitVec 32) = 0 at bad
  exact (by decide +kernel : (1 : BitVec 32) ≠ 0) bad

theorem corrupt_selector_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (corrupt 152)) (constraints Airbender.Blake2Worker.Fixed.table) := by
  intro holds
  have bad := (native_worker_finalization holds).selector
  change (1 : F) = 0 at bad
  exact one_ne_zero bad

theorem inactive_requests_retained :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeWorkerExtendedOutput.inactive_requests_retained
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
      ∀ w ∈ Airbender.NativeTokenLedger.workerRows workers, Airbender.NativeWorkerFinalization.RowEffects w :=
  native_counted_worker_finalization publicSetup embed memory ch pc gamma decoder config accepted image lookups identity
end Airbender.Tests.NativeWorkerFinalization
