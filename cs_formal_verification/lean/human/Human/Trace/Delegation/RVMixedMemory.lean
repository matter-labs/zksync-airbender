module
public import Human.Helpers.Delegation.RVMixedMemory
public import Human.Helpers.Memory.RVHistory

@[expose] public section

namespace Airbender.Delegation.Caller
open Trace

/-- RV sibling of `MixedMemoryEffects`: mixed architectural transport and worker operations on the actual native port
    values; every transfer executes once in native clock order as RV cell reads/writes from the public initial
    `RV.State` (`RVHistory`; RAM cells include READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END`) and reaches all
    shared terminal cells in one final `RV.State`. -/
structure RVMixedMemoryEffects [Fact p.Prime] (data : RVRequestTrace p)
    (before : RV.State) (cells : List Cell) : Prop where
  requests : RVRequestBinding data before
  zeroReads : ∀ edge ∈ data.mixedSteps,
    edge.1.address = (Cell.register 0).addressCode → edge.1.value = 0
  words : ∀ edge ∈ data.mixedSteps, edge.1.word.Bounded ∧ edge.2.word.Bounded
  terminal : ∀ token ∈ data.machine.terminalMemory, token.word.Bounded
  addresses : ∀ edge ∈ data.mixedSteps, ∃ cell ∈ cells,
    cell.addressCode = edge.1.address ∧ cell.addressWord.Bounded
  operations : ∀ row ∈ data.workers.rows, WorkerEffect row
  execution : ∃ (events : List MemoryAccess) (after : RV.State),
    events.Perm (data.mixedSteps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧
    RVHistory cells events before after ∧
    ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
      cell.addressCode = token.address ∧ cell.readRV after = some token.word.toBitVec

end Airbender.Delegation.Caller
