import Airbender.Review.Circuits.ReducedMachine.WorkerClockFixturesTheorems
import Mathlib.Tactic.FinCases

namespace Airbender.Tests.NativeWorkerClockFixtures
open Airbender.NativeWorkerClockFixtures Airbender.Verification
open Airbender.Blake2Worker Airbender.Blake2Worker.Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem multiplicity_one (zeroClock : Bool) : assignment zeroClock constraintsABI.multiplicity = 1 :=
  Airbender.NativeWorkerClockFixtureProofs.multiplicity zeroClock

theorem abi_high_zero (zeroClock : Bool) : assignment zeroClock constraintsABI.offsetHigh = 0 := rfl

theorem zero_raw_clock : Airbender.NativeActiveWorkerClocks.workerClock (assignment true) = (0,0) :=
  Airbender.NativeWorkerClockFixtureProofs.raw_clock true

theorem wide_raw_clock : Airbender.NativeActiveWorkerClocks.workerClock (assignment false) = (0,524288) :=
  Airbender.NativeWorkerClockFixtureProofs.raw_clock false

theorem all_borrows_zero (zeroClock : Bool) (slot : Fin 43) : assignment zeroClock (742+3*slot.val) = 0 := by
  fin_cases slot <;> cases zeroClock <;> decide +kernel

theorem all_round_flags_zero (zeroClock : Bool) (slot : Fin 13) : assignment zeroClock (138+slot.val) = 0 := by
  fin_cases slot <;> cases zeroClock <;> decide +kernel

theorem all_raw_old_times (zeroClock : Bool) (slot : Fin 43) :
    (Airbender.NativeWorkerClockProgress.readToken (assignment zeroClock) slot).time = (0,if zeroClock then -1 else 0) :=
  Airbender.NativeWorkerClockFixtureProofs.read_time zeroClock slot

theorem all_read_values_zero (zeroClock : Bool) (slot : Fin 43) :
    (Airbender.NativeWorkerClockProgress.readToken (assignment zeroClock) slot).value = 0 := by
  fin_cases slot <;> cases zeroClock <;> decide +kernel

theorem all_writes_same_clock (zeroClock : Bool) (slot : Fin 43) :
    (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey (assignment zeroClock) slot true)).time =
      Airbender.NativeActiveWorkerClocks.workerClock (assignment zeroClock) :=
  Airbender.NativeActiveWorkerClockProofs.write_clock (assignment zeroClock) slot

theorem zero_reads_unbounded (slot : Fin 43) :
    ¬ (Airbender.NativeWorkerClockProgress.readClock (assignment true) slot).Bounded :=
  Airbender.NativeWorkerClockFixtureProofs.zero_old_unbounded slot

theorem wide_processor_unbounded : ¬ (Airbender.NativeWorkerClockProgress.clock (assignment false)).Bounded :=
  Airbender.NativeWorkerClockFixtureProofs.wide_clock_unbounded

theorem wide_reads_bounded (slot : Fin 43) :
    (Airbender.NativeWorkerClockProgress.readClock (assignment false) slot).Bounded := by
  rw [Airbender.NativeWorkerClockProgress.readClock,all_raw_old_times]
  change (0 : Nat) < 524288 ∧ (0 : Nat) < 524288
  decide +kernel

theorem pointers_control_zero (zeroClock : Bool) : assignment zeroClock 2 = 0 ∧ assignment zeroClock 3 = 0 ∧
    assignment zeroClock 100 = 0 ∧ assignment zeroClock 101 = 0 ∧ assignment zeroClock 134 = 0 ∧
    assignment zeroClock 135 = 0 ∧ assignment zeroClock 136 = 0 ∧ assignment zeroClock 137 = 0 := by
  cases zeroClock <;> decide +kernel

/-- Complete LOCAL acceptance only; no global/whole-worker/physical witness. -/
theorem complete_local_acceptance (zeroClock : Bool) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment zeroClock)) (constraints Fixed.table) ∧
      LocalProcessingAccepted (assignment zeroClock) :=
  ⟨native_worker_clock_fixture_body zeroClock,native_worker_clock_fixture_processing zeroClock⟩
end Airbender.Tests.NativeWorkerClockFixtures
