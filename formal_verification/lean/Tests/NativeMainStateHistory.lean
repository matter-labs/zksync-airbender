import Airbender.Review.Circuits.ReducedMachine.MainStateHistoryTheorems
import Airbender.Proofs.ReducedMachine.NativeCSRPositiveWitness

namespace Airbender.Tests.NativeMainStateHistory
open Airbender.NativeMainStateHistory Airbender.NativeMainStateHistoryProofs Airbender.NativeTokenLedger
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

private abbrev csr := Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment

theorem select_actual_execute_only : selectAssignments [csr false,csr true] = [csr true] := by
  simp [selectAssignments,Airbender.ReducedMachine.Native.importedConstraintsTraceColumns,
    Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment]

/-- No caller request is filtered or claimed fulfilled by main-state selection. -/
theorem inactive_csr_request_stays_observed : selectAssignments [csr false] = [] ∧ csr false 92 = 1 := by
  constructor
  · simp [selectAssignments,Airbender.ReducedMachine.Native.importedConstraintsTraceColumns,
      Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment]
  · decide +kernel

theorem actual_pc_and_clock_observations : (state (mainPCKey (csr true) false)).pc = (0,0) ∧
    (state (mainPCKey (csr true) false)).timestamp = (4,0) ∧
    (state (mainPCKey (csr true) true)).pc = (4,0) ∧
    (state (mainPCKey (csr true) true)).timestamp = (8,0) := by decide +kernel

/-- Raw observed fields are kept. This is not an accepted bounded-clock row. -/
theorem raw_state_limbs_retained :
    (state (⟨#v[65536,700000],#v[600000,700001]⟩ : PCKey)).pc = (65536,700000) ∧
    (state (⟨#v[65536,700000],#v[600000,700001]⟩ : PCKey)).timestamp = (600000,700001) := by decide +kernel

theorem initialization_is_not_a_state (w : Nat → F) (write : Bool) :
    (activeRowTokens w write).filterMap stateProjection =
      if w Airbender.ReducedMachine.Native.importedConstraintsTraceColumns.execute = 1 then [mainPCKey w write] else [] :=
  row_states w write

theorem workers_are_not_pc_edges (assignments : List (Nat → F)) (write : Bool) :
    (assignments.flatMap fun w => workerRowTokens w write).filterMap stateProjection = [] :=
  worker_states assignments write

private def inputs : PublicBoundary := ⟨fun _ => ⟨0,#v[0,0]⟩,0,#v[4,0]⟩
private def memory : MemoryKeyChallenges F := ⟨0,0,0,0,0,0,0⟩
private def pc : PCChallenges F := ⟨1,0,0,0⟩
private def processor : ProcessorChallenges F := ⟨0,0,0,0⟩
private def config : WorkerConfiguration Unit := ⟨.security80,()⟩
private def batch : WorkerBatch Unit F := ⟨0,[]⟩
private def inverse : BoundaryInverses F := ⟨1,1⟩

/-- Complete EMPTY selected normalized component, not a nonempty worker/main or
    physical verifier witness. All32 public registers and PC are still present. -/
theorem empty_component : MainWorkerAccepted (RingHom.id F) memory processor pc config [] batch inputs inverse := by
  constructor
  · simp
  · constructor
    · constructor
      · rfl
      · simp [batch]
      · simp [batch]
      · decide +kernel
    · constructor
      · rfl
      · decide +kernel
      · decide +kernel
    · decide +kernel

theorem empty_full_logical_matching : LogicalMatching ([] : List (MainProof F)) batch inputs := by
  unfold LogicalMatching
  decide +kernel

theorem empty_checked_history : Effects ([] : List (MainProof F)) inputs :=
  native_main_state_history (RingHom.id F) memory processor pc config empty_component empty_full_logical_matching

theorem empty_derived_clock_and_path :
    (Trace.timeOfPair (state (finalPCKey inputs)).timestamp).value = 4 ∧
      ∃ path, Path ([] : List (MainProof F)) inputs path := by
  have effects := empty_checked_history
  exact ⟨by simpa [rows,selectAssignments,mainRows] using effects.terminal,effects.path⟩

theorem wrong_empty_terminal_rejected :
    ¬ Effects ([] : List (MainProof F)) {inputs with finalTime := #v[8,0]} := by
  intro effects
  have clock := effects.terminal
  have wrong : (Trace.timeOfPair (state (finalPCKey {inputs with finalTime := #v[8,0]})).timestamp).value = 8 := by decide +kernel
  rw [wrong] at clock
  simp [rows,selectAssignments,mainRows] at clock

theorem complete_conditional_main_history {Setup R : Type} [Field R] (embed : F →+* R)
    (ch : MemoryKeyChallenges R) (worker : ProcessorChallenges R) (stateChallenges : PCChallenges R)
    (configuration : WorkerConfiguration Setup) {mains : List (MainProof R)} {workers : WorkerBatch Setup R}
    {boundary : PublicBoundary} {inverses : BoundaryInverses R}
    (accepted : MainWorkerAccepted embed ch worker stateChallenges configuration mains workers boundary inverses)
    (matching : LogicalMatching mains workers boundary) : Effects mains boundary :=
  native_main_state_history embed ch worker stateChallenges configuration accepted matching

end Airbender.Tests.NativeMainStateHistory
