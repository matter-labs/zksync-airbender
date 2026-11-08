module
public import Human.Helpers.Delegation.RVMemory

@[expose] public section

namespace Airbender.Delegation
open Trace

/-- RV sibling of `MemoryExecution`: every imported delegation access executes once, in native timestamp order, as
    RV cell reads/writes from the public initial state (RAM cells are `mem`, INCLUDING READ-WRITE ACCESS TO THE
    SHADOW RAM BELOW `ROM_END`, `RV.State.delegationRAM`); untouched aligned cells keep their reads; every declared
    terminal token is read from the resulting state. -/
def RVMemoryExecution (data : MemoryData p) (before : RV.State) (cells : List Cell) : Prop :=
  ∃ (events : List MemoryAccess) (after : RV.State),
    events.Perm (data.steps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧
    RVHistory cells events before after ∧
    (∀ edge ∈ data.steps, RVPortExecution cells events before after edge) ∧
    (∀ cell : Cell, cell.Aligned → (∀ edge ∈ data.steps, edge.1.address ≠ cell.addressCode) →
      ∀ value, cell.readRV before = some value → cell.readRV after = some value) ∧
    ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
      cell.readRV after = some (memoryWord token.value)

/-- RV sibling of `TraceMapping`: the same final state executes every native access once and agrees with every
    terminal token. -/
structure RVTraceMapping (data : Delegation.MemoryData p) (initial after : RV.State)
    (cells : List Cell) : Prop where
  history : ∃ events : List MemoryAccess, events.Perm (data.steps.map transferEvent) ∧
    RVHistory cells events initial after
  finalCells : ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
    cell.readRV after = some token.word.toBitVec

end Airbender.Delegation
