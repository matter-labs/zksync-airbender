import Human.Helpers.Delegation.SharedMemory

namespace Airbender.Delegation.Caller
open Trace

/-- Actual caller and worker accesses execute together in initialized Sail cells.
    Source x0 values and worker addresses are derived from the shared paths.
    This is architectural memory transport, not whole-call ABI or ISA execution;
    span segmentation and zero-clock fulfillment remain explicit open tasks. -/
structure SharedMemoryEffects [Fact p.Prime] (data : RequestTrace p)
    (before : Reference.RiscV.Sail.State) (cells : List Cell) : Prop where
  /-- Public instructions identify actual workers and their invocation clocks. -/
  requests : RequestBinding data before
  /-- Each caller's native source is exactly the canonical zero word. -/
  sources : ∀ row ∈ data.callers, (sourceToken row.assignment).value = 0
  /-- Public initialized addresses bound every worker's native port address. -/
  addresses : ∀ row ∈ data.workers.rows, ∀ port ∈ row.ports,
    (port.address.word row.assignment).Bounded
  /-- The same history contains every caller/worker transfer exactly once,
      follows native timestamp order and reaches all shared terminal values. -/
  execution : ∃ (events : List MemoryAccess) (after : Reference.RiscV.Sail.State),
    events.Perm (data.sharedSteps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧
    Trace.SailHistory cells events before after ∧
    ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
      cell.addressCode = token.address ∧ cell.read after = .ok token.word.toBitVec after

end Airbender.Delegation.Caller
