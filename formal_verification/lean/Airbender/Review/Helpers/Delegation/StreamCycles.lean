import Airbender.Review.Trace.Modular.ExternalCalls
import Airbender.Review.Helpers.Delegation.StreamMemory
import Airbender.Review.Helpers.Delegation.Schedule
import Airbender.Review.Helpers.Memory.SailHistory

namespace Airbender.Delegation.Caller
open Trace

/-- The actual caller's full CSR and invocation select its native worker rows. -/
noncomputable def RequestTrace.cycleWorkers [Fact p.Prime]
    (data : RequestTrace p) (row : Trace.Row p PooledFamily) : List (Delegation.Row p) := by
  classical
  exact if row ∈ data.callers then
    data.workers.rows.filter fun worker => decide (Requests.fulfillment worker = Requests.caller row.assignment)
  else []

/-- One pooled cycle contains its actual architectural ports and issued workers. -/
noncomputable def RequestTrace.cycleSteps [Fact p.Prime]
    (data : RequestTrace p) (row : Trace.Row p PooledFamily) :=
  (machinePorts row).toList.map (fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)) ++
    (data.cycleWorkers row).flatMap Delegation.Row.memorySteps

/-- Exact instruction cuts inside the one native mixed memory history. -/
def CycleExecution [Fact p.Prime] (data : RequestTrace p) (cells : List Cell)
    (events : List MemoryAccess) (initial finalState : Reference.RiscV.Sail.State)
    (row : Trace.Row p PooledFamily) : Prop :=
  ∃ earlier current newer before after,
    events = newer ++ current ++ earlier ∧
    current.Perm (data.cycleSteps row |>.map transferEvent) ∧
    SailHistory cells earlier initial before ∧ SailHistory cells current before after ∧
    SailHistory cells newer after finalState

/-- An original clause retires between its actual pooled instruction cuts. -/
def RetiresCycle (cells : List Cell) (events : List MemoryAccess)
    (initial finalState : Reference.RiscV.Sail.State) (row : Trace.Row p PooledFamily)
    (clause : SailRV32.SailM SailRV32.ExecutionResult) : Prop :=
  ∃ before after,
    SailHistory cells (events.filter fun event => decide
      (event.1 ≤ (timeOfPair row.start.timestamp).value)) initial before ∧
    SailHistory cells (events.filter fun event => decide
      ((timeOfPair row.start.timestamp).value < event.1 ∧
        event.1 ≤ (timeOfPair row.finish.timestamp).value)) before after ∧
    SailHistory cells (events.filter fun event => decide
      ((timeOfPair row.finish.timestamp).value < event.1)) after finalState ∧
    Reference.Sail.run (Reference.RiscV.Sail.normalStep clause)
      (retiredState before row.start.word.toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after row.finish.word.toBitVec)

/-- The complete successful reference call at the exact native caller cuts. -/
def FullCallerCycle [Fact p.Prime] (data : RequestTrace p) (initial finalState : Reference.RiscV.Sail.State)
    (cells : List Cell) (events : List MemoryAccess) (row : Trace.Row p PooledFamily) : Prop :=
  ∃ before after,
    SailHistory cells (events.filter fun event => decide (event.1 ≤ startClock row)) initial before ∧
    SailHistory cells (events.filter fun event => decide
      (startClock row < event.1 ∧ event.1 ≤ finishClock row)) before after ∧
    SailHistory cells (events.filter fun event => decide (finishClock row < event.1)) after finalState ∧
    ∃ entry ∈ data.program, nativeQuery row.assignment = query entry ∧
      row.start.word.toBitVec = entry.pc ∧ entry.SourceWith before decoderFields ∧
      UnifiedReduced.Caller.FullCall entry.data.family before after ∧
      UnifiedReduced.Caller.FullRetirement entry.data.family
        (retiredState before row.start.word.toBitVec) (retiredState after row.finish.word.toBitVec)

end Airbender.Delegation.Caller

namespace Airbender.AddSub.Modular.External.Caller
open Trace
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- The public pooled clause, exact stream increment and actual native retirement. -/
def OrdinaryCycle [Fact p.Prime] (stream : List (BitVec 32))
    (program : List PooledProgramEntry) (trace : PooledTrace p)
    (cells : List Cell) (events : List MemoryAccess)
    (initial finalState : Reference.RiscV.Sail.State) (row : Trace.Row p PooledFamily) : Prop :=
  ∃ entry ∈ program, entry.data.family = row.family ∧ row.decoderQuery = entry.query ∧
    ∃ clause next,
      External.clause stream (External.readIndex trace row) entry.instruction = some (clause, next) ∧
      next = External.readIndex trace row + (if External.isRead row then 1 else 0) ∧
      Delegation.Caller.RetiresCycle cells events initial finalState row clause

end Airbender.AddSub.Modular.External.Caller
