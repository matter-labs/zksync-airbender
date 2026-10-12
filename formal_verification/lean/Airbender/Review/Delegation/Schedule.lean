import Airbender.Review.Delegation.RequestTrace

namespace Airbender.Delegation.Caller
open Trace
variable {Kind : Type} [CircuitLayout Kind]

/-- The machine's imported starting clock, interpreted as a natural number.
    The shared state path proves its limbs are canonical. -/
abbrev startClock (row : Trace.Row p Kind) : Nat := row.clock

/-- The same row's imported ending clock. Native equations advance it by four. -/
def finishClock (row : Trace.Row p Kind) : Nat :=
  (decodeTimestamp row.assignment row.columns.finalTime).value

/-- Where one issued worker falls inside its caller's native cycle.
    These are conclusions from clock equations and request matching. Worker
    reads can refer to older writes; `writes` describes the new write clock.
    Clean access times add one to native clocks to reserve time zero for seeds. -/
structure WorkerSlot (caller : Trace.Row p Kind) (worker : Delegation.Row p) : Prop where
  /-- The actual invocation occurs one tick after the caller starts. -/
  invocation : (decodeTimestamp worker.assignment worker.columns.invocation).value = startClock caller + 1
  /-- Every native worker port writes three ticks after the caller starts. -/
  writes : ∀ port ∈ worker.ports,
    (timeOfPair (worker.writeToken port).time).value = startClock caller + 3
  /-- The caller finishes at tick four, after the worker writes. -/
  finish : finishClock caller = startClock caller + 4

/-- Exact scheduling of issued workers, without an assumed ordering or count.
    Every live worker has one caller and occupies that caller's cycle. Native
    zero-clock workers have no caller; this known gap is exposed, not excluded. -/
structure WorkerSchedule [Fact p.Prime] (data : RequestTrace p) : Prop where
  /-- Each actual caller has exactly one native worker in its cycle. -/
  callers : ∀ caller ∈ data.callers, ∃! worker,
    worker ∈ data.workers.rows ∧ Requests.fulfillment worker = Requests.caller caller.assignment ∧
      WorkerSlot caller worker
  /-- Every nonzero invocation belongs to exactly one actual caller. -/
  workers : ∀ worker ∈ data.workers.rows, Requests.Live (Requests.fulfillment worker) →
    ∃! caller, caller ∈ data.callers ∧
      Requests.fulfillment worker = Requests.caller caller.assignment ∧ WorkerSlot caller worker
  /-- An active worker is unissued exactly when its invocation clock is zero. -/
  unissued : ∀ worker ∈ data.workers.rows,
    (¬ ∃ caller ∈ data.callers, Requests.fulfillment worker = Requests.caller caller.assignment) ↔
      (Requests.fulfillment worker).time = (0, 0)
  /-- No other instruction starts strictly inside an issued caller's cycle. -/
  separated : ∀ caller ∈ data.callers, ∀ row ∈ data.machine.rows,
    ¬ (startClock caller < startClock row ∧ startClock row < finishClock caller)

end Airbender.Delegation.Caller
