module
public import Human.Trace.Delegation.RVRequestTrace
public import Human.Helpers.Delegation.RVRequestEffects

@[expose] public section

namespace Airbender.Delegation.Caller
open Trace

/-- The matched worker pool executes its native ports in RV cells
    (`RVRequestExecution`; RAM cells include READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END`) and satisfies the
    existing operation references on those port values. -/
structure RVRequestOperationEffects [Fact p.Prime] (data : RVRequestTrace p)
    (before : RV.State) (cells : List Cell) : Prop where
  execution : RVRequestExecution data before cells
  words : WordBounds data.workers
  operations : ∀ row ∈ data.workers.rows, WorkerEffect row

end Airbender.Delegation.Caller
