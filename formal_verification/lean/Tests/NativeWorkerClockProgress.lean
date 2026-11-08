import Airbender.Review.Circuits.ReducedMachine.WorkerClockProgressTheorems
import Tests.NativeBlake2PositiveRow
import Tests.NativeInitializationBatch

namespace Airbender.Tests.NativeWorkerClockProgress
open Airbender.NativeWorkerClockProgress Airbender.Verification Airbender.Blake2Worker.Native
open Airbender.NativeInitializationBatch (Proof)
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
abbrev F := Airbender.NativeWorkerClockProgress.F
private def positive := Airbender.Blake2Worker.PositiveRow.assignment
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem all43_exact_old_times (w : Nat → F) (slot : Fin 43) :
    (readToken w slot).time = (w (memoryAccess slot).readTime[0],w (memoryAccess slot).readTime[1]) :=
  Airbender.NativeWorkerClockProgressProofs.read_time w slot

theorem old_value_address_retained (w : Nat → F) (slot : Fin 43) :
    (readToken w slot).address = Airbender.NativeMemoryTokens.encodeAddress (quotientMemoryKey w slot false).address ∧
    (readToken w slot).value = Nat.pair ((quotientMemoryKey w slot false).value[0]).val
      ((quotientMemoryKey w slot false).value[1]).val := ⟨rfl,rfl⟩

theorem positive_clock : (clock positive).value = 3 ∧ (clock positive).Bounded := by
  change (3 : Nat) = 3 ∧ (3 : Nat) < 524288 ∧ (0 : Nat) < 524288
  decide +kernel

theorem positive_all43_old_clocks (slot : Fin 43) : readClock positive slot = ⟨0,0⟩ := by
  have low := Airbender.Tests.NativeBlake2PositiveRow.all_old_times_zero slot (0 : Fin 2)
  have high := Airbender.Tests.NativeBlake2PositiveRow.all_old_times_zero slot (1 : Fin 2)
  rw [readClock,Airbender.NativeWorkerClockProgressProofs.read_time]
  rw [show positive (memoryAccess slot).readTime[0] = 0 from low,
    show positive (memoryAccess slot).readTime[1] = 0 from high]
  rfl

theorem positive_all43_strict_progress (slot : Fin 43) : (readClock positive slot).value < (clock positive).value :=
  Airbender.NativeWorkerClockProgressProofs.strict_read Airbender.Blake2Worker.PositiveRow.native_positive_body
    slot (by rfl) positive_clock.2 (by
      change (readClock positive slot).Bounded
      rw [positive_all43_old_clocks]
      constructor <;> decide +kernel)

theorem complete_positive_local_progress : LocalProgress positive :=
  native_worker_local_clock_progress Airbender.Blake2Worker.PositiveRow.native_positive_body

/-- DATA under test; unlike the prior time3 fixture this fails the COMPLETE
    native BODY. No active-zero global witness or defect is inferred. -/
private def activeZero (column : Nat) : F := if column=0 then 1 else 0

theorem active_zero_oldzero_body_rejected : ¬ FlatOperation.ConstraintsHoldFlat (environment activeZero) (constraints Airbender.Blake2Worker.Fixed.table) := by
  intro holds
  have unbounded := Airbender.NativeWorkerClockProgressProofs.zero_unbounded holds (by rfl) (by rfl) (0 : Fin 43)
  have bounded : (readClock activeZero (0 : Fin 43)).Bounded := by
    rw [readClock,Airbender.NativeWorkerClockProgressProofs.read_time]
    change ((activeZero 743).val < 524288 ∧ (activeZero 744).val < 524288)
    decide +kernel
  exact unbounded bounded

/-- PURE order control, not a native accepted cycle. -/
theorem bounded_cycle_rejected (a b : Nat) : ¬ (a < b ∧ b < a) := by omega

theorem duplicate_port_occurrences (w : Nat → F) :
    ([0,0] : List (Fin 43)).map (readToken w) = [readToken w 0,readToken w 0] := rfl

theorem complete_empty_progress : Effects (Airbender.NativeMemoryHistory.emptyWorkers Unit F) :=
  native_worker_clock_progress _ _ _ _ _ _ Airbender.Tests.NativeInitializationBatch.empty_combined_component

theorem complete_conditional_progress {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) : Effects batch :=
  native_worker_clock_progress embed memory ch pc gamma config accepted

theorem complete_zero_source {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    {w : Nat → F} (present : w ∈ Airbender.NativeTokenLedger.workerRows batch)
    (active : w constraintsABI.multiplicity = 1)
    (zero : Airbender.NativeActiveWorkerClocks.workerClock w = (0,0)) :
    ∀ slot : Fin 43, UnboundedWriter batch (readToken w slot) :=
  (native_worker_clock_progress embed memory ch pc gamma config accepted).zero w present active zero
end Airbender.Tests.NativeWorkerClockProgress
