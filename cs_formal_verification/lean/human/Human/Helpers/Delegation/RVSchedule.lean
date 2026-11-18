module
public import Human.Helpers.Delegation.Schedule
public import Human.Helpers.Delegation.RVRequestTrace

@[expose] public section

namespace Airbender.Delegation.Caller
open Trace

/-- Worker schedule over `RVRequestTrace` (state-free): every live worker has one caller
    and occupies that caller's native cycle; zero-clock workers are exposed as unissued. -/
structure RVWorkerSchedule [Fact p.Prime] (data : RVRequestTrace p) : Prop where
  callers : ∀ caller ∈ data.callers, ∃! worker,
    worker ∈ data.workers.rows ∧ Requests.fulfillment worker = Requests.caller caller.assignment ∧
      WorkerSlot caller worker
  workers : ∀ worker ∈ data.workers.rows, Requests.Live (Requests.fulfillment worker) →
    ∃! caller, caller ∈ data.callers ∧
      Requests.fulfillment worker = Requests.caller caller.assignment ∧ WorkerSlot caller worker
  unissued : ∀ worker ∈ data.workers.rows,
    (¬ ∃ caller ∈ data.callers, Requests.fulfillment worker = Requests.caller caller.assignment) ↔
      (Requests.fulfillment worker).time = (0, 0)
  separated : ∀ caller ∈ data.callers, ∀ row ∈ data.machine.rows,
    ¬ (startClock caller < startClock row ∧ startClock row < finishClock caller)

end Airbender.Delegation.Caller
