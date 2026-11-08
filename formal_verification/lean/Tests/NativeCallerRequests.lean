import Airbender.Review.Circuits.ReducedMachine.CallerRequestsTheorems
import Tests.NativeInitializationBatch
import Airbender.Proofs.ReducedMachine.NativeCSRPositiveWitness

namespace Airbender.Tests.NativeCallerRequests
open Airbender.NativeCallerRequests Airbender.Verification Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
abbrev F := Airbender.NativeCallerRequests.F
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- PURE packed-mask controls, not accepted rows or decoder witnesses.
theorem mask_zero : csrMaskBit (fun _ => (0 : F)) = 0 := by decide +kernel

theorem low_window : csrMaskBit (fun _ => (127 : F)) = 0 := by decide +kernel

theorem csr_boundary : csrMaskBit (fun _ => (128 : F)) = 1 := by decide +kernel

theorem csr_instruction_mask : csrMaskBit (fun _ => (129 : F)) = 1 := by decide +kernel

theorem mop_selector_off : csrMaskBit (fun _ => (34819 : F)) = 0 ∧
    csrMaskBit (fun _ => (133123 : F)) = 0 ∧ csrMaskBit (fun _ => (67587 : F)) = 0 := by decide +kernel

theorem upper_mask : csrMaskBit (fun _ => (262143 : F)) = 1 := by decide +kernel

private def w (active : Bool) := Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment active

theorem inactive_complete_shape : RowEffects (w false) :=
  native_caller_request_shape (Airbender.ReducedMachine.NativeCSRPositiveWitness.body false)

theorem active_complete_shape : RowEffects (w true) :=
  native_caller_request_shape (Airbender.ReducedMachine.NativeCSRPositiveWitness.body true)

/-- Same complete BODY fixture retains request1 with execute0. Not a full
    auxiliary/global/source-worker/physical witness or native defect. -/
theorem inactive_request_retained : w false importedConstraintsTraceColumns.execute = 0 ∧
    (csrRequest (w false)).multiplicity = 1 ∧ csrMaskBit (w false) = 1 := by decide +kernel

theorem oracle_erased (active : Bool) : csrOracleWord (w active) = ⟨0,0⟩ := by
  have effects := native_caller_request_shape (Airbender.ReducedMachine.NativeCSRPositiveWitness.body active)
  have present : (csrRequest (w active)).multiplicity ≠ 0 := by cases active <;> decide +kernel
  exact (effects.present present).2.2.2

theorem zero_gate_fields {setup : Table F (fields 4)} {row : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment row) (importedConstraints setup))
    (disabled : csrMaskBit row = 0) : csrRequest row = ⟨0,0,some 0,3⟩ :=
  (native_caller_request_shape holds).disabled disabled

/-- ENTIRE contradiction over an ABSTRACT setup before native pool/data. -/
private theorem reject_gate {setup : Table F (fields 4)} {row : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment row) (importedConstraints setup))
    (off : row 24 = 0) (on : row 92 = 1) : False := by
  have relation := (Airbender.NativeCallerRequestProofs.relations holds).2.1
  rw [off,on,zero_mul] at relation
  exact one_ne_zero relation

private def corrupted (column : Nat) : F := if column = 24 then 0 else w false column

theorem corrupt_selector_rejected : ¬ FlatOperation.ConstraintsHoldFlat (environment corrupted)
    (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table) := by
  intro accepted
  exact reject_gate accepted (by rfl) (by decide +kernel)

theorem translated_clock_list : (([4,8] : List Nat).map (fun time => time+3)).Nodup :=
  Airbender.NativeCallerRequestProofs.translated_unique [4,8] id (fun time => time+3)
    (fun _ _ => rfl) (by decide +kernel)

theorem duplicate_clock_preserved : ([4,4] : List Nat).map (fun time => time+3) = [7,7] ∧
    ¬ (([4,4] : List Nat).map (fun time => time+3)).Nodup := by decide +kernel

private def emptyInputs : PublicBoundary := ⟨fun _ => ⟨0,#v[0,0]⟩,0,#v[4,0]⟩

theorem complete_empty_requests : Effects ([] : List (Airbender.NativeInitializationBatch.Proof F)) :=
  native_all_caller_requests _ _ _ _ _ _ Airbender.Tests.NativeInitializationBatch.empty_combined_component

theorem complete_empty_clocks : ActiveClockEffects ([] : List (Airbender.NativeInitializationBatch.Proof F)) emptyInputs :=
  native_active_main_caller_clocks _ _ _ _ _ _ Airbender.Tests.NativeInitializationBatch.empty_combined_component

theorem complete_conditional_joint {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    Effects proofs ∧ ActiveClockEffects proofs inputs :=
  ⟨native_all_caller_requests embed memory ch pc gamma config accepted,
    native_active_main_caller_clocks embed memory ch pc gamma config accepted⟩

theorem actual_raw_offset (active : Bool) :
    (csrCallerObservation (.mk .reduced (w active))).time = (7,0) := by cases active <;> decide +kernel
end Airbender.Tests.NativeCallerRequests
