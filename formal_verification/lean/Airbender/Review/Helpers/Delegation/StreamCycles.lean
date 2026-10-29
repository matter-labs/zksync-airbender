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

end Airbender.Delegation.Caller
