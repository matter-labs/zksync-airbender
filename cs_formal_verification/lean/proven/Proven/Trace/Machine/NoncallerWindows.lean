module
public import Proven.Trace.Machine.AnyWorker
public import Proven.Trace.Machine.RequestWindows

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- A unrolled cycle without a request has no worker memory events. -/
theorem unrolled_worker_window_empty {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {row : Trace.Row babyBearModulus PooledFamily} (member : row ∈ trace.rows)
    (notCalled : row ∉ unrolledCallers trace) :
    (workers.steps.map transferEvent).filter (fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro event present retained
  rw [← any_worker_steps, List.map_flatMap] at present
  obtain ⟨source, included, actual⟩ := List.mem_flatMap.mp present
  have issued : source.request ∈ workers.fulfillments := by
    rw [← any_worker_requests]
    exact List.mem_map.mpr ⟨source, included, rfl⟩
  have clocks := (unrolled_worker_clocks accepted initial aligned).1
  have window := unrolled_request_window accepted initial aligned member issued
    (any_worker_event_time clocks included actual)
  exact notCalled (window.mp (of_decide_eq_true retained)).1

/-- A unified cycle without a request has no worker memory events. -/
theorem unified_worker_window_empty {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {row : Trace.Row babyBearModulus UnifiedFamily} (member : row ∈ trace.rows)
    (notCalled : row ∉ trace.rows.filter (fun source => decide (UnifiedReduced.Caller.Selected source.assignment))) :
    (workers.steps.map transferEvent).filter (fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro event present retained
  rw [← any_worker_steps, List.map_flatMap] at present
  obtain ⟨source, included, actual⟩ := List.mem_flatMap.mp present
  have issued : source.request ∈ workers.fulfillments := by
    rw [← any_worker_requests]
    exact List.mem_map.mpr ⟨source, included, rfl⟩
  have clocks := (unified_worker_clocks accepted initial aligned).1
  have window := unified_request_window accepted initial aligned member issued
    (any_worker_event_time clocks included actual)
  exact notCalled (window.mp (of_decide_eq_true retained)).1

end Airbender.Trace.Machine.Proofs
