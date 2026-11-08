module
public import Human.Helpers.Delegation.RVSharedMemory
public import Human.Helpers.Memory.RVHistory

@[expose] public section

namespace Airbender.Delegation.Caller
open Trace

/-- RV sibling of `SharedMemoryEffects`: caller and worker accesses execute together as RV cell reads/writes from the
    public initial `RV.State` (`RVHistory`; RAM cells include READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END`),
    in native clock order, reaching every shared terminal value. -/
structure RVSharedMemoryEffects [Fact p.Prime] (data : RVRequestTrace p)
    (before : RV.State) (cells : List Cell) : Prop where
  requests : RVRequestBinding data before
  sources : ∀ row ∈ data.callers, (sourceToken row.assignment).value = 0
  addresses : ∀ row ∈ data.workers.rows, ∀ port ∈ row.ports,
    (port.address.word row.assignment).Bounded
  execution : ∃ (events : List MemoryAccess) (after : RV.State),
    events.Perm (data.sharedSteps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧
    RVHistory cells events before after ∧
    ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
      cell.addressCode = token.address ∧ cell.readRV after = some token.word.toBitVec

/-- RV sibling of `SharedOperationEffects`: requests, RV transfers and the four operation references on the same
    architectural pool, with every word bound proved. -/
structure RVSharedOperationEffects [Fact p.Prime] (data : RVRequestTrace p)
    (before : RV.State) (cells : List Cell) : Prop where
  memory : RVSharedMemoryEffects data before cells
  words : RVSharedWordBounds data
  operations : ∀ row ∈ data.workers.rows, WorkerEffect row

end Airbender.Delegation.Caller
