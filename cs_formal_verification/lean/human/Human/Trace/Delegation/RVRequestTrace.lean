import Human.Trace.Delegation.RVExecution
import Human.Helpers.Delegation.RVRequestTrace

namespace Airbender.Delegation.Caller
open Trace

/-- RV sibling of `RequestExecution`: request binding and the same worker pool's accesses executed as RV cell
    reads/writes (`RVMemoryExecution`; RAM cells include READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END`). -/
structure RVRequestExecution [Fact p.Prime] (data : RVRequestTrace p)
    (before : RV.State) (cells : List Cell) : Prop where
  requests : RVRequestBinding data before
  memory : MemorySoundness data.workers
  execution : RVMemoryExecution data.workers before cells

end Airbender.Delegation.Caller
