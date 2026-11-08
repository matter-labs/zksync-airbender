import Airbender.Review.Circuits.ReducedMachine.ActiveWorkerClocksTheorems
import Tests.NativeInitializationBatch

namespace Airbender.Tests.NativeActiveWorkerClocks
open Airbender.NativeActiveWorkerClocks
open Airbender.NativeActiveWorkerClockProofs (write_clock padding_clock bounded_or_active sampled_property active_writer_member unbounded_source)
open Airbender.NativeInitializationBatch (Proof)
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- DATA ONLY: these rows are not asserted to satisfy the352body/296lookups,
    source auxiliary/global components or physical verifier. -/
private def wide (column : Nat) : F := if column = 740 then 700000 else if column = 741 then 17 else if column = 0 then 1 else 0
private def activeZero (column : Nat) : F := if column = 0 then 1 else 0

theorem zero_clock_data : workerClock (fun _ => 0) = (0,0) := rfl

theorem wide_clock_data : workerClock wide = (700000,17) := rfl

theorem wide_clock_not_bounded : ¬ (Trace.timeOfPair (workerClock wide)).Bounded := by
  rw [wide_clock_data]
  change ¬ ((700000 : F).val < 524288 ∧ (17 : F).val < 524288)
  decide +kernel

/-- Activity alone is not a nonzero-clock claim. This PUREprojection is not
    a full accepted m1zero-clock witness or absence-of-enforcement evidence. -/
theorem active_zero_clock_data : activeZero constraintsABI.multiplicity = 1 ∧ workerClock activeZero = (0,0) := ⟨rfl,rfl⟩

theorem all43_common_write_clock (w : Nat → F) : ∀ slot : Fin 43,
    (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true)).time = workerClock w := write_clock w

theorem last_actual_write_clock (w : Nat → F) :
    (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w (42 : Fin 43) true)).time = workerClock w := write_clock w 42

theorem arbitrary_raw_limbs_retained (w : Nat → F) :
    workerClock w = (w constraintsABI.writeTime[0],w constraintsABI.writeTime[1]) := rfl

theorem duplicate_sampling : ([0,0] : List Nat).flatMap (fun a => (List.range 1).map fun _ => a) = [0,0] ∧
    ∀ value ∈ ([0,0] : List Nat).flatMap (fun a => (List.range 1).map fun _ => a), value = 0 := by
  refine ⟨rfl,sampled_property [0,0] (fun a _ => a) 1 (fun a => a = 0) ?_⟩
  intro a member i _
  simpa using member

theorem conditional_padding_clock {w : Nat → F} (accepted : LocalProcessingAccepted w) (zero : w constraintsABI.multiplicity = 0) :
    workerClock w = (0,0) := padding_clock (Airbender.Blake2Worker.ProcessingProofs.effects accepted.conventions) zero

theorem conditional_local_activity {w : Nat → F} (accepted : LocalProcessingAccepted w) :
    (Trace.timeOfPair (workerClock w)).Bounded ∨ w constraintsABI.multiplicity = 1 := bounded_or_active accepted

theorem exact_actual_source_member {Setup R : Type} [Field R] {batch : WorkerBatch Setup R}
    {token : Trace.MemoryToken mersenne31Modulus} (source : ActiveWriter batch token) :
    token ∈ Airbender.NativeMemoryHistory.workerWrites batch := active_writer_member source

/-- COMPLETEEMPTY existing stronger acceptance, not a nonempty worker witness. -/
theorem complete_empty_sources : Effects ([] : List (Proof F)) (Airbender.NativeMemoryHistory.emptyWorkers Unit F) :=
  native_active_worker_clock_sources _ _ _ _ _ _ Airbender.Tests.NativeInitializationBatch.empty_combined_component

theorem complete_conditional_sources {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    Effects proofs batch := native_active_worker_clock_sources embed memory ch pc gamma config accepted

theorem exact_unbounded_raw_source {Setup R : Type} [Field R] {batch : WorkerBatch Setup R}
    {token : Trace.MemoryToken mersenne31Modulus} (source : (Trace.timeOfPair token.time).Bounded ∨ ActiveWriter batch token)
    (unbounded : ¬ (Trace.timeOfPair token.time).Bounded) :
    ∃ w ∈ Airbender.NativeTokenLedger.workerRows batch, ∃ slot : Fin 43,
      w constraintsABI.multiplicity = 1 ∧ token = Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true) ∧
        token.time = workerClock w ∧ ¬ (Trace.timeOfPair (workerClock w)).Bounded := unbounded_source source unbounded

end Airbender.Tests.NativeActiveWorkerClocks
