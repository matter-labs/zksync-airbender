import Airbender.Proofs.Trace.StreamCount
import Airbender.Proofs.UnifiedReduced.StreamCycles

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
open Caller.Proofs
set_option warningAsError true

/-- Native clock constraints determine one cycle's exact stream increment. -/
theorem native_cycle_count
    {data : RequestTrace babyBearModulus} {initial : State} {ca : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data initial ca)
    {row : Trace.Row babyBearModulus UnifiedFamily} (member : row ∈ data.machine.rows) :
    ExternalStream.countBefore Trace.Row.clock Stream.isRead data.machine.rows
        (Delegation.Caller.finishClock row) =
      ExternalStream.countBefore Trace.Row.clock Stream.isRead data.machine.rows row.clock +
        (if Stream.isRead row then 1 else 0) := by
  have clocks := machine_clock_facts (by decide) (by decide) accepted inputs member
  rw [clocks.2]
  apply ExternalStream.Proofs.count_after_cycle Trace.Row.clock Stream.isRead member
    (machine_clocks_unique (by decide) (by decide) accepted inputs)
  intro item present
  exact (machine_clock_facts (by decide) (by decide) accepted inputs present).1

/-- No native row consumes a stream word before the public start state. -/
theorem native_initial_count
    {data : RequestTrace babyBearModulus} {initial : State} {ca : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data initial ca) :
    ExternalStream.countBefore Trace.Row.clock Stream.isRead data.machine.rows
      (timeOfPair data.machine.initial.timestamp).value = 0 := by
  have intervals := state_clock_interval (by decide) (by decide) accepted.constraints
    accepted.states inputs.initialClock inputs.initialAligned
  apply ExternalStream.Proofs.count_at_start
  intro row member
  exact (intervals row member).1

/-- The terminal clock accounts for every external-read row exactly once. -/
theorem native_terminal_count
    {data : RequestTrace babyBearModulus} {initial : State} {ca : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data initial ca) :
    ExternalStream.countBefore Trace.Row.clock Stream.isRead data.machine.rows
      (timeOfPair data.machine.terminal.timestamp).value = Stream.readCount data.machine := by
  have intervals := state_clock_interval (by decide) (by decide) accepted.constraints
    accepted.states inputs.initialClock inputs.initialAligned
  apply ExternalStream.Proofs.count_at_finish
  intro row member
  have bound := (intervals row member).2
  change row.clock + 4 ≤ (timeOfPair data.machine.terminal.timestamp).value at bound
  omega

end Airbender.UnifiedReduced.Caller.Stream.Proofs
