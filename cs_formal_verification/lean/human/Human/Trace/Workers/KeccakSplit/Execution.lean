import Human.Trace.Workers.KeccakSplit.Inputs

namespace Airbender.Keccak.Split.Native
open Trace

/-- Actual Sail execution of every imported split-worker access, once each, from
    the public initial state, as `Delegation.MemoryExecution` states it for the other
    delegation workers: events in native timestamp order, every port's read/write
    position in that history, untouched aligned cells and the machine configuration
    preserved, and every terminal token read from the final state. -/
def MemoryExecution (data : MemoryData p) (before : Reference.RiscV.Sail.State)
    (cells : List Cell) : Prop :=
  ∃ (events : List MemoryAccess) (after : Reference.RiscV.Sail.State),
    events.Perm (data.steps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧
    SailHistory cells events before after ∧
    (∀ edge ∈ data.steps, Delegation.PortExecution cells events before after edge) ∧
    (∀ cell : Cell, cell.Aligned → (∀ edge ∈ data.steps, edge.1.address ≠ cell.addressCode) →
      ∀ value, cell.read before = .ok value before → cell.read after = .ok value after) ∧
    (Reference.RiscV.Sail.Configured before → Reference.RiscV.Sail.Configured after) ∧
    ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
      cell.read after = .ok (memoryWord token.value) after

/-- The final state executes every native access exactly once, and every native
    terminal value agrees with it. -/
structure TraceMapping (data : MemoryData p) (initial after : Reference.RiscV.Sail.State)
    (cells : List Cell) : Prop where
  history : ∃ events : List MemoryAccess, events.Perm (data.steps.map transferEvent) ∧
    SailHistory cells events initial after
  finalCells : ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
    cell.read after = .ok token.word.toBitVec after

end Airbender.Keccak.Split.Native
