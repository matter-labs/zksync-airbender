import Human.Helpers.Delegation.SpanABI
import Human.Helpers.Memory.InitialImageRV

namespace Airbender.Delegation.Caller
open Trace

/-- RV sibling of `HashSpan.Protocol`: the same modeled tables, homogeneous family and span-size ABI; the public
    mode/control register is read from an `RV.State` (`Cell.readRV`). -/
structure HashSpan.RVProtocol [Fact p.Prime] (workers : MemoryData p)
    (before : RV.State) (span : HashSpan) : Prop where
  tables : workers.setup = modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ workers.rows, row.family = span.family
  controlStart : (Cell.register span.controlRegister).readRV before = some span.controlStart
  calls : workers.rows.length = span.callCount

end Airbender.Delegation.Caller
