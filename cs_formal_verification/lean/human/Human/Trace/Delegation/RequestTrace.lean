import Human.Trace.Delegation.Execution
import Human.Helpers.Delegation.RequestTrace

namespace Airbender.Delegation.Caller
open Trace

/-- Request binding and actual initialized worker memory share the same rows.
    This exposes native reads/writes and terminal values, without adding per-row
    ranges or clock-room premises. Whole-machine architectural composition and
    exclusion of extra zero-clock workers remain separate obligations. -/
structure RequestExecution [Fact p.Prime] (data : RequestTrace p)
    (before : Reference.RiscV.Sail.State) (cells : List Cell) : Prop where
  /-- Actual public instructions issue the exact worker requests. -/
  requests : RequestBinding data before
  /-- Initialized native paths enforce latest-write/read consistency and bounds. -/
  memory : MemorySoundness data.workers
  /-- Those same worker accesses run on Sail cells and reach native terminal values. -/
  execution : MemoryExecution data.workers before cells

end Airbender.Delegation.Caller
