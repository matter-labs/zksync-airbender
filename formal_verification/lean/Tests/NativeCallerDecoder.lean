import Airbender.Review.Circuits.ReducedMachine.CallerDecoderTheorems
import Tests.NativeCSRPositive

namespace Airbender.Tests.NativeCallerDecoder
open Airbender.NativeCallerDecoder
open Airbender.ReducedMachine.Native Airbender.Trace Airbender.Verification
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Pure projection controls, not global accepted source witnesses. -/
theorem shift_projected : (Airbender.NativeCallerDecoder.decoderFields
    (.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SLL))).isSome = true := rfl

theorem arithmetic_projected : (Airbender.NativeCallerDecoder.decoderFields
    (.ITYPE (1,.Regidx 1,.Regidx 3,.ADDI))).isSome = true := rfl

theorem load_projected : (Airbender.NativeCallerDecoder.decoderFields
    (.LOAD (0,.Regidx 1,.Regidx 3,false,4))).isSome = true := rfl

theorem store_projected : (Airbender.NativeCallerDecoder.decoderFields
    (.STORE (0,.Regidx 2,.Regidx 1,4))).isSome = true := rfl

private def csrEntry : Program := Airbender.Tests.NativeCSRPositive.entry.mapFamily Sum.inr

theorem csr_projected : Airbender.NativeCallerDecoder.decoderFields csrEntry.instruction = some csrEntry.data := rfl

theorem csr_query_preserved : csrEntry.query (p := mersenne31Modulus) = Airbender.Tests.NativeCSRPositive.entry.query := rfl

theorem csr_bit_present : ((csrMask : F).val / 128 % 2) = 1 := by decide +kernel

theorem shift_bit_absent (mode : ShiftMode) (useRegister : Bool) : ((mode.mask useRegister : F).val / 128 % 2) = 0 :=
  Airbender.NativeCallerDecoderProofs.shift_bit mode useRegister

theorem nonboolean_two_rejected : ¬ ((2 : F) = 0 ∨ (2 : F) = 1) := by decide +kernel

private theorem actual_query (active : Bool) :
    decoderQuery (Airbender.Tests.NativeCSRPositive.nativeRow active).assignment = csrEntry.query := by
  cases active <;> decide +kernel

/-- Reuses complete LOCAL117eq22lookup BODY; no counted/global/physical witness. -/
theorem active_local_validity : RowEffects (Airbender.Tests.NativeCSRPositive.nativeRow true).assignment csrEntry :=
  native_decoded_caller_request (Airbender.ReducedMachine.NativeCSRPositiveWitness.body true) csr_projected (actual_query true)

/-- Inactive physical requests remain possible at this complete LOCAL interface. -/
theorem inactive_local_validity : RowEffects (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment csrEntry :=
  native_decoded_caller_request (Airbender.ReducedMachine.NativeCSRPositiveWitness.body false) csr_projected (actual_query false)

theorem inactive_still_requests :
    (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment importedConstraintsTraceColumns.execute = 0 ∧
      csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow false).assignment = ⟨1,1991,some 0,3⟩ :=
  Airbender.Tests.NativeCSRPositive.inactive_body_still_requests.2

theorem full_local_negative_nonboolean :
    (csrRequest (Airbender.Tests.NativeCSRPositive.nativeRow true).assignment).multiplicity ≠ 2 := by
  rw [Airbender.Tests.NativeCSRPositive.actual_request]
  decide +kernel

theorem complete_conditional_joint {Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Mode) (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainDecoder.Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainDecoder.SourceAccepted publicSetup embed memory ch pc gamma decoder config batch workers inputs inverse)
    {before : Reference.RiscV.Sail.State} {count : Nat}
    (image : setupImage before count 20 = some publicSetup)
    (lookups : Airbender.NativeMainDecoder.LogicalLookups publicSetup batch) :
    Airbender.NativeMainBatch.Effects batch.main ∧
      Airbender.NativeMainDecoder.DecoderEffects publicSetup embed decoder batch ∧
      Airbender.NativeWorkerClockProgress.Effects workers ∧ Effects before publicSetup batch :=
  native_counted_caller_requests publicSetup embed memory ch pc gamma decoder config accepted image lookups
end Airbender.Tests.NativeCallerDecoder
