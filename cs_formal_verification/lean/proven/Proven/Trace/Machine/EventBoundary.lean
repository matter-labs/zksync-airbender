module
public import Proven.Trace.Machine.CPUEvents
public import Proven.Trace.Machine.PathBounds
public import Proven.Trace.Machine.CallerTimes
public import Proven.Trace.Machine.AnyWorker

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Every CPU port event lies strictly after boot and at or before the terminal clock. -/
theorem cpu_event_boundary {Kind : Type} [CircuitLayout Kind] [ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (constraints : ∀ row ∈ trace.rows, FlatOperation.ConstraintsHoldFlat
      (Verification.environment row.assignment) (row.constraints trace.rom))
    (states : (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start))
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {row : Trace.Row babyBearModulus Kind} (member : row ∈ trace.rows) {ports : Array MemoryPort}
    (native : ∀ port ∈ ports, port ∈ row.ports) {event : MemoryAccess} (present : event ∈ cpuEvents row ports) :
    (timeOfPair trace.initial.timestamp).value < event.1 ∧ event.1 ≤ (timeOfPair trace.terminal.timestamp).value := by
  have range := cpu_cycle_clock_bounds constraints states initial aligned member
  have clock := state_clock_inputs (by decide) (by decide) constraints states initial aligned row member
  have advance := ClockLaws.advance (by decide) (by decide) trace.rom row (constraints row member) clock.1
  obtain ⟨offset, bound, time⟩ := cpu_event_time constraints states initial aligned member native present
  change (decodeTimestamp row.assignment row.columns.finalTime).value = row.clock + 4 at advance
  omega

/-- Complete unrolled request matching places every worker invocation inside the machine endpoints. -/
theorem unrolled_worker_boundary {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {request : Requests.Request babyBearModulus} (present : request ∈ workers.fulfillments) :
    (timeOfPair trace.initial.timestamp).value < (timeOfPair request.time).value + 3 ∧
      (timeOfPair request.time).value + 3 ≤ (timeOfPair trace.terminal.timestamp).value := by
  obtain ⟨row, called, same⟩ := List.mem_map.mp ((unrolled_requests_complete accepted initial aligned).mem_iff.mpr present)
  have member := (unrolled_caller_member called).1
  have range := cpu_cycle_clock_bounds accepted.constraints accepted.states initial aligned member
  have clock := state_clock_inputs (by decide) (by decide) accepted.constraints accepted.states initial aligned row member
  have advance := ClockLaws.advance (by decide) (by decide) trace.rom row (accepted.constraints row member) clock.1
  have issued := unrolled_request_time accepted initial aligned called
  rw [← same, issued]
  change (decodeTimestamp row.assignment row.columns.finalTime).value = row.clock + 4 at advance
  omega

/-- Complete unified request matching gives the same worker endpoint bounds. -/
theorem unified_worker_boundary {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {request : Requests.Request babyBearModulus} (present : request ∈ workers.fulfillments) :
    (timeOfPair trace.initial.timestamp).value < (timeOfPair request.time).value + 3 ∧
      (timeOfPair request.time).value + 3 ≤ (timeOfPair trace.terminal.timestamp).value := by
  obtain ⟨row, called, same⟩ := List.mem_map.mp ((unified_requests_complete accepted initial aligned).mem_iff.mpr present)
  have member := (List.mem_filter.mp called).1
  have range := cpu_cycle_clock_bounds accepted.constraints accepted.states initial aligned member
  have clock := state_clock_inputs (by decide) (by decide) accepted.constraints accepted.states initial aligned row member
  have advance := ClockLaws.advance (by decide) (by decide) trace.rom row (accepted.constraints row member) clock.1
  have issued := unified_request_time accepted initial aligned member
  rw [← same, issued]
  change (decodeTimestamp row.assignment row.columns.finalTime).value = row.clock + 4 at advance
  omega

end Airbender.Trace.Machine.Proofs
