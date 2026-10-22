import Human.Helpers.Delegation.WorkerContext

namespace Airbender.Delegation
open Trace

/-- Actual Sail cell execution of every imported delegation access, once each,
    from the public initial state. Events follow native timestamp order; ties
    are permitted because all delegation ports use the same clock slot.

    Every port exposes its actual position and read/write states in that history.
    Every declared terminal token is read from the resulting Sail state.
    Other aligned cells retain their initial successful reads, including cells
    outside the tracked domain; the public Machine configuration is preserved.
    This connects the memory argument to registers/RAM; operation semantics,
    caller ABI and whole hash scheduling are separate claims. -/
def MemoryExecution (data : MemoryData p) (before : Reference.RiscV.Sail.State)
    (cells : List Cell) : Prop :=
  ∃ (events : List MemoryAccess) (after : Reference.RiscV.Sail.State),
    events.Perm (data.steps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧
    SailHistory cells events before after ∧
    (∀ edge ∈ data.steps, PortExecution cells events before after edge) ∧
    (∀ cell : Cell, cell.Aligned → (∀ edge ∈ data.steps, edge.1.address ≠ cell.addressCode) →
      ∀ value, cell.read before = .ok value before → cell.read after = .ok value after) ∧
    (Reference.RiscV.Sail.Configured before →
      Reference.RiscV.Sail.Configured after) ∧
    ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
      cell.read after = .ok (memoryWord token.value) after

/-- The same final state executes every native request access exactly once.
    Matching supplies the initial reads and connects every final token to RAM
    or a GPR; this is a proved conclusion, not a supplied execution/result. -/
structure TraceMapping (data : Delegation.MemoryData p) (initial after : Reference.RiscV.Sail.State)
    (cells : List Cell) : Prop where
  /-- Actual Sail transfers of the imported native accesses. -/
  history : ∃ events : List MemoryAccess, events.Perm (data.steps.map transferEvent) ∧
    Trace.SailHistory cells events initial after
  /-- Every native terminal value agrees with the actual final Sail state. -/
  finalCells : ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
    cell.read after = .ok token.word.toBitVec after

end Airbender.Delegation
