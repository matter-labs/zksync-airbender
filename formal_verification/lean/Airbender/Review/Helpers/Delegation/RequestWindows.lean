import Airbender.Review.Helpers.Delegation.Schedule
import Airbender.Review.Helpers.Delegation.NativeWindows

namespace Airbender.Delegation.Caller
open Trace
variable {Kind : Type} [CircuitLayout Kind]

/-- Actual caller rows starting between two instruction-boundary clocks. -/
def windowCallers (callers : List (Trace.Row p Kind)) (lower upper : Nat) :=
  callers.filter fun caller => decide (lower ≤ startClock caller ∧ startClock caller < upper)

/-- Exact caller/worker matching inside a native window. Cuts lie on the
    four-tick stride and follow clock two; zero-clock workers remain in the prefix. -/
structure RequestWindowBinding [Fact p.Prime] (callers : List (Trace.Row p Kind))
    (workers : MemoryData p) (lower upper : Nat) : Prop where
  /-- Full-width CSR and raw invocation tokens agree, including multiplicity. -/
  fulfilled : ((windowCallers callers lower upper).map fun caller => Requests.caller caller.assignment).Perm
    ((workers.windowRows lower upper).map Requests.fulfillment)
  /-- Each selected caller has exactly one actual worker in that window. -/
  callerMatches : ∀ caller ∈ windowCallers callers lower upper, ∃! worker,
    worker ∈ workers.windowRows lower upper ∧
      Requests.fulfillment worker = Requests.caller caller.assignment ∧ WorkerSlot caller worker
  /-- Each selected worker belongs to exactly one actual selected caller. -/
  workerMatches : ∀ worker ∈ workers.windowRows lower upper, ∃! caller,
    caller ∈ windowCallers callers lower upper ∧
      Requests.fulfillment worker = Requests.caller caller.assignment ∧ WorkerSlot caller worker
  /-- Surplus zero-clock rows are retained before the cut, with all their effects. -/
  unissued : ∀ worker ∈ workers.rows, (Requests.fulfillment worker).time = (0, 0) →
    worker ∈ workers.prefixRows lower ∧ worker ∉ workers.windowRows lower upper

end Airbender.Delegation.Caller
