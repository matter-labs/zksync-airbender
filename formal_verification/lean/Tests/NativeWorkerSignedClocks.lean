import Airbender.Review.Circuits.ReducedMachine.WorkerSignedClocksTheorems
import Tests.NativeBlake2PositiveRow

namespace Airbender.Tests.NativeWorkerSignedClocks
open Airbender.NativeWorkerSignedClocks Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Pure raw-clock controls, not new accepted source/physical witnesses. -/
theorem zero_value : value ((0 : F),0) = 0 := by decide +kernel

theorem low_sentinel : value ((-1 : F),0) = -1 := by decide +kernel

theorem high_sentinel : value ((524287 : F),-1) = -1 := by decide +kernel

theorem sentinel_pairs_distinct : ((-1 : F),0) ≠ (524287,-1) := by decide +kernel

theorem wide_carry_alias : value ((524288 : F),0) = value (0,1) := by decide +kernel

theorem wide_still_not_canonical : ¬ (Trace.timeOfPair ((524288 : F),0)).Bounded := by
  intro bounded
  have low := bounded.1
  change 524288 < 524288 at low
  omega

private theorem negativeDomain : Airbender.NativeCallerClockDomain.Domain (Trace.timeOfPair ((-1 : F),0)) := by
  constructor <;> decide +kernel

theorem domain_allows_minus_one :
    Airbender.NativeCallerClockDomain.Domain (Trace.timeOfPair ((-1 : F),0)) ∧ value ((-1 : F),0) = -1 :=
  ⟨negativeDomain,low_sentinel⟩

theorem domain_lower_boundary : -1 ≤ value ((-1 : F),0) :=
  Airbender.NativeWorkerSignedClockProofs.domain_lower negativeDomain

/-- Reuse old FULL LOCAL native BODY; this does not fabricate initialized
    history for its zero-pointer aliases or a nonempty global accepted proof. -/
private abbrev localRow := Airbender.Blake2Worker.PositiveRow.assignment

theorem local_body : FlatOperation.ConstraintsHoldFlat (Airbender.Verification.environment localRow)
    (constraints Airbender.Blake2Worker.Fixed.table) := Airbender.Blake2Worker.PositiveRowProofs.body

theorem local_clock_value : workerValue localRow = 3 := by decide +kernel

private theorem local_read_time (slot : Fin 43) :
    (Airbender.NativeWorkerClockProgress.readToken localRow slot).time = (0,0) := by
  rw [Airbender.NativeWorkerClockProgressProofs.read_time]
  have low := Airbender.Tests.NativeBlake2PositiveRow.all_old_times_zero slot (0 : Fin 2)
  have high := Airbender.Tests.NativeBlake2PositiveRow.all_old_times_zero slot (1 : Fin 2)
  change localRow (memoryAccess slot).readTime[0] = 0 at low
  change localRow (memoryAccess slot).readTime[1] = 0 at high
  rw [low,high]

theorem local_all_read_values (slot : Fin 43) : readValue localRow slot = 0 := by
  rw [readValue,local_read_time]
  exact zero_value

theorem local_all_progress (slot : Fin 43) : readValue localRow slot < workerValue localRow := by
  apply Airbender.NativeWorkerSignedClockProofs.local_progress local_body
    (Airbender.Tests.NativeBlake2PositiveRow.multiplicity_one)
  · change Airbender.NativeCallerClockDomain.Domain (Trace.timeOfPair ((3 : F),0))
    constructor <;> decide +kernel
  · rw [local_read_time]
    constructor <;> decide +kernel

theorem active_zero_excluded {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    (result : Effects proofs batch) {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows batch)
    (active : w constraintsABI.multiplicity = 1) : Airbender.NativeActiveWorkerClocks.workerClock w ≠ (0,0) :=
  result.zero w member active

theorem self_dependency_rejected {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    (result : Effects proofs batch) (w : Nat → F) : ¬ Dependency batch w w := by
  intro edge
  exact (lt_irrefl (workerValue w)) (Airbender.NativeWorkerSignedClockProofs.dependency_order result edge)

theorem two_cycle_rejected {Setup R : Type} [Field R]
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {batch : WorkerBatch Setup R}
    (result : Effects proofs batch) {a b : Nat → F}
    (first : Dependency batch a b) : ¬ Dependency batch b a := by
  intro second
  have lower := Airbender.NativeWorkerSignedClockProofs.dependency_order result first
  have upper := Airbender.NativeWorkerSignedClockProofs.dependency_order result second
  omega

theorem complete_conditional_counted {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers ∧ NoWorkerCycles workers :=
  native_counted_worker_signed_progress embed memory ch pc gamma config accepted identity
end Airbender.Tests.NativeWorkerSignedClocks
