module
public import Proven.Trace.Machine.AnyWorker
public import Proven.Trace.Machine.EventGroups
public import Proven.Trace.Machine.RequestWindows

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Unique invocation times identify worker rows in the common native view. -/
theorem any_worker_times_unique {workers : WorkerPools babyBearModulus}
    (unique : (workers.fulfillments.map Requests.Request.time).Nodup) :
    ((anyWorkers workers).map fun source => source.request.time).Nodup := by
  have result : (((anyWorkers workers).map AnyWorker.request).map Requests.Request.time).Nodup := by
    rw [any_worker_requests]
    exact unique
  simpa only [List.map_map, Function.comp_def] using result

/-- Filtering all native worker events by one request retains its unique worker row. -/
theorem worker_request_group {workers : WorkerPools babyBearModulus}
    (unique : (workers.fulfillments.map Requests.Request.time).Nodup)
    {chosen : AnyWorker babyBearModulus} (member : chosen ∈ anyWorkers workers)
    {request : Requests.Request babyBearModulus} (matched : chosen.request = request)
    (keep : MemoryAccess → Bool)
    (selected : ∀ source ∈ anyWorkers workers, ∀ event ∈ source.steps.map transferEvent,
      keep event = true ↔ source.request = request) :
    (workers.steps.map transferEvent).filter keep = chosen.steps.map transferEvent := by
  have distinct := any_worker_times_unique unique
  rw [← any_worker_steps, List.map_flatMap]
  apply event_group_single (anyWorkers workers) (fun source => source.request.time)
    (fun source => source.steps.map transferEvent) keep distinct member
  intro source included event present
  rw [selected source included event present]
  constructor
  · intro same
    exact List.inj_on_of_nodup_map distinct included member (congrArg Requests.Request.time (same.trans matched.symm))
  · intro same
    subst source
    exact matched

/-- Full request membership supplies a unique submitted worker for the caller occurrence. -/
theorem submitted_worker {workers : WorkerPools babyBearModulus}
    (unique : (workers.fulfillments.map Requests.Request.time).Nodup)
    {request : Requests.Request babyBearModulus} (present : request ∈ workers.fulfillments) :
    ∃ chosen ∈ anyWorkers workers, chosen.request = request ∧
      ∀ source ∈ anyWorkers workers, source.request = request → source = chosen := by
  rw [← any_worker_requests] at present
  obtain ⟨chosen, included, same⟩ := List.mem_map.mp present
  refine ⟨chosen, included, same, ?_⟩
  intro source member matched
  exact List.inj_on_of_nodup_map (any_worker_times_unique unique) member included
    (congrArg Requests.Request.time (matched.trans same.symm))

/-- The unrolled worker contribution in a caller cycle is the complete matched native row. -/
theorem unrolled_worker_window_group {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {row : Trace.Row babyBearModulus PooledFamily} (called : row ∈ unrolledCallers trace)
    {chosen : AnyWorker babyBearModulus} (member : chosen ∈ anyWorkers workers)
    (matched : chosen.request = Requests.caller row.assignment) :
    (workers.steps.map transferEvent).filter (fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)) =
      chosen.steps.map transferEvent := by
  have clocks := unrolled_worker_clocks accepted initial aligned
  apply worker_request_group clocks.2 member matched
  intro source included event present
  have issued : source.request ∈ workers.fulfillments := by
    rw [← any_worker_requests]
    exact List.mem_map.mpr ⟨source, included, rfl⟩
  have window := unrolled_request_window accepted initial aligned (unrolled_caller_member called).1 issued
    (any_worker_event_time clocks.1 included present)
  simpa only [decide_eq_true_eq, called, true_and] using window

/-- Unified caller cycles retain the same complete native worker contribution. -/
theorem unified_worker_window_group {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {row : Trace.Row babyBearModulus UnifiedFamily}
    (called : row ∈ trace.rows.filter (fun source => decide (UnifiedReduced.Caller.Selected source.assignment)))
    {chosen : AnyWorker babyBearModulus} (member : chosen ∈ anyWorkers workers)
    (matched : chosen.request = UnifiedReduced.Caller.request row.assignment) :
    (workers.steps.map transferEvent).filter (fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)) =
      chosen.steps.map transferEvent := by
  have clocks := unified_worker_clocks accepted initial aligned
  apply worker_request_group clocks.2 member matched
  intro source included event present
  have issued : source.request ∈ workers.fulfillments := by
    rw [← any_worker_requests]
    exact List.mem_map.mpr ⟨source, included, rfl⟩
  have window := unified_request_window accepted initial aligned (List.mem_filter.mp called).1 issued
    (any_worker_event_time clocks.1 included present)
  simpa only [decide_eq_true_eq, called, true_and] using window

end Airbender.Trace.Machine.Proofs
