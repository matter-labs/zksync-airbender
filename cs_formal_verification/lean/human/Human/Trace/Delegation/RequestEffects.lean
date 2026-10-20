import Human.Trace.Delegation.RequestTrace
import Human.Helpers.Delegation.RequestEffects

namespace Airbender.Delegation.Caller
open Trace

/-- The same matched worker pool executes its native ports in Sail cells and
    satisfies the existing operation references. Request binding identifies the
    actual worker for every decoded caller. This claim retains the separate
    worker memory pool, round ABI and zero-clock-fulfillment boundaries. -/
structure RequestOperationEffects [Fact p.Prime] (data : RequestTrace p)
    (before : Reference.RiscV.Sail.State) (cells : List Cell) : Prop where
  /-- Original public callers, exact request clocks and actual worker memory. -/
  execution : RequestExecution data before cells
  /-- Shared initialization and operation queries derive all RV32 word bounds. -/
  words : WordBounds data.workers
  /-- Every actual worker matches its named reference on those same port values. -/
  operations : ∀ row ∈ data.workers.rows, WorkerEffect row

end Airbender.Delegation.Caller
