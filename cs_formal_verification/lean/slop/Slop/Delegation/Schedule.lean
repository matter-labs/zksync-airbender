module
public import Human.Helpers.Delegation.Schedule
public import Slop.Delegation.RequestTrace

@[expose] public section

namespace Airbender.Delegation.Caller.Proofs
open Trace Arithmetic
set_option warningAsError true

theorem worker_slot_of_clock [Fact p.Prime] {Kind : Type} [CircuitLayout Kind]
    (hp : timestampBase < p) {caller : Trace.Row p Kind} {worker : Delegation.Row p}
    (issued : (timeOfPair (Requests.caller caller.assignment).time).value = startClock caller + 1)
    (advance : finishClock caller = startClock caller + 4)
    (bound : (decodeTimestamp worker.assignment worker.columns.invocation).Bounded)
    (room : (decodeTimestamp worker.assignment worker.columns.invocation).lo + 2 < timestampBase)
    (same : Requests.fulfillment worker = Requests.caller caller.assignment) : WorkerSlot caller worker := by
  have invocation : (decodeTimestamp worker.assignment worker.columns.invocation).value = startClock caller + 1 :=
    (congrArg (fun request : Requests.Request p => (timeOfPair request.time).value) same).trans issued
  refine ⟨invocation, ?_, advance⟩
  intro port present
  have offset := Delegation.Proofs.port_offset worker present
  have written := (Trace.Proofs.write_time_of_room hp
    (base := rawPair worker.assignment worker.columns.invocation) (offset := port.clock.offset)
    bound (by simpa only [offset, decodeTimestamp, rawPair] using room)).2
  change (timeOfPair (worker.writeToken port).time).value =
    (decodeTimestamp worker.assignment worker.columns.invocation).value + port.clock.offset at written
  rw [written, offset, invocation]

end Airbender.Delegation.Caller.Proofs
