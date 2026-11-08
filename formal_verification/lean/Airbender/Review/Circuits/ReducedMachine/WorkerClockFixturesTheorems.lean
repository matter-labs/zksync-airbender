import Airbender.Proofs.ReducedMachine.NativeWorkerClockFixtures

namespace Airbender.NativeWorkerClockFixtures
open Airbender.Verification Airbender.Blake2Worker.Native

/-- Every actual native equation/lookup for both explicit LOCAL fixtures.
    This is not source/global/physical acceptance or initialized execution. -/
theorem native_worker_clock_fixture_body (zeroClock : Bool) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment zeroClock)) (constraints Airbender.Blake2Worker.Fixed.table) :=
  NativeWorkerClockFixtureProofs.body zeroClock

/-- Complete native LOCAL processing conventions, with active multiplicity.
    No caller issuance, memory history, round schedule or worker result supplied. -/
theorem native_worker_clock_fixture_processing (zeroClock : Bool) : LocalProcessingAccepted (assignment zeroClock) :=
  NativeWorkerClockFixtureProofs.local_processing zeroClock
end Airbender.NativeWorkerClockFixtures
