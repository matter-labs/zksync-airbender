module
public import Proven.Trace.Machine.MemoryClocks

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The unrolled caller issues its full CSR request at the second cycle tick. -/
theorem unrolled_request_time {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {row : Trace.Row babyBearModulus PooledFamily} (member : row ∈ unrolledCallers trace) :
    (timeOfPair (Requests.caller row.assignment).time).value = row.clock + 1 := by
  have included := unrolled_caller_member member
  have clock := state_clock_inputs (by decide : 2 * timestampBase + 4 < babyBearModulus)
    (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1)
    accepted.constraints accepted.states initial aligned row included.1
  have time := (write_time (by decide : timestampBase < babyBearModulus)
    (base := rawPair row.assignment row.columns.initialTime) clock.1 clock.2 (show 1 < 4 by decide)).2
  have offset : Requests.callerPort.clock.offset = 1 := rfl
  simpa only [Requests.caller, offset, Row.columns, included.2, CircuitLayout.columns,
    AddSub.importedConstraintsTraceColumns, Row.clock, decodeTimestamp, timeOfPair, rawPair] using time

/-- Unified callers use the same request time and keep the full CSR identifier. -/
theorem unified_request_time {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {row : Trace.Row babyBearModulus UnifiedFamily} (member : row ∈ trace.rows) :
    (timeOfPair (UnifiedReduced.Caller.request row.assignment).time).value = row.clock + 1 := by
  have clock := state_clock_inputs (by decide : 2 * timestampBase + 4 < babyBearModulus)
    (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1)
    accepted.constraints accepted.states initial aligned row member
  have time := (write_time (by decide : timestampBase < babyBearModulus)
    (base := rawPair row.assignment row.columns.initialTime) clock.1 clock.2 (show 1 < 4 by decide)).2
  have offset : Requests.callerPort.clock.offset = 1 := rfl
  simpa only [UnifiedReduced.Caller.request, Requests.caller, offset,
    Row.columns, CircuitLayout.columns, AddSub.importedConstraintsTraceColumns,
    UnifiedReduced.importedConstraintsTraceColumns, Row.clock, decodeTimestamp, timeOfPair, rawPair] using time

end Airbender.Trace.Machine.Proofs
