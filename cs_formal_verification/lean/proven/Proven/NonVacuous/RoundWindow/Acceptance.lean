module
public import Proven.NonVacuous.RoundWindow.CPU
public import Proven.NonVacuous.RoundWindow.Memory
public import Proven.NonVacuous.RoundWindow.Window

@[expose] public section
namespace Airbender.NonVacuous.RoundWindow
open Trace Trace.Machine
set_option warningAsError true

/-- The ten unrolled callers and ten round workers meet every machine acceptance premise. -/
theorem unrolled_accepted : UnrolledAcceptance unrolledTrace workers unrolledProgram where
  toWorkersAccepted := workers_accepted
  constraints := unrolled_constraints
  active := unrolled_active_rows
  states := unrolled_states
  decoded := unrolled_decoded
  requests := unrolled_requests
  memory := unrolled_memory

/-- The unified caller block meets the same constraints and exact matching premises. -/
theorem unified_accepted : UnifiedAcceptance unifiedTrace workers unifiedProgram where
  toWorkersAccepted := workers_accepted
  constraints := unified_constraints
  active := unified_active_rows
  states := unified_states
  decoded := unified_decoded
  requests := unified_requests
  memory := unified_memory

/-- The actual unrolled requests fill the one complete round interval. -/
theorem unrolled_profile :
    HashWindowProfile ((unrolledCallers unrolledTrace).map
      fun row => Delegation.Requests.caller row.assignment) windows := by
  rw [unrolled_calls]
  exact protocol_profile

/-- The actual unified requests fill the same complete round interval. -/
theorem unified_profile :
    HashWindowProfile ((unifiedTrace.rows.filter
      fun row => decide (UnifiedReduced.Caller.Selected row.assignment)).map
      fun row => UnifiedReduced.Caller.request row.assignment) windows := by
  rw [unified_calls]
  exact protocol_profile

/-- The submitted unrolled CPU trace contains the full ten-call path. -/
theorem unrolled_rows_nonempty : unrolledTrace.rows ≠ [] := by
  intro empty
  have size := unrolled_rows_length
  rw [empty] at size
  contradiction

/-- The submitted unified CPU trace contains the full ten-call path. -/
theorem unified_rows_nonempty : unifiedTrace.rows ≠ [] := by
  intro empty
  have size := unified_rows_length
  rw [empty] at size
  contradiction

/-- The submitted standard worker pool contains every round of the protocol. -/
theorem worker_rows_nonempty : workers.standard.rows ≠ [] := by
  intro empty
  have size := worker_rows_length
  rw [empty] at size
  contradiction

end Airbender.NonVacuous.RoundWindow
