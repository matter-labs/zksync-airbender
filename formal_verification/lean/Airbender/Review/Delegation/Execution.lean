import Airbender.Review.Delegation.Memory
import Airbender.Proofs.Trace.SailHistory

namespace Airbender.Delegation
open Trace Trace.Proofs

/-- One native port's actual read/write position in the shared Sail history.
    Earlier accesses produce `middle`; this port reads there and writes `later`;
    remaining accesses produce the final state. Timestamp ties are still ordered
    internally. This is memory transport, separate from a whole delegation call. -/
def PortExecution (cells : List Cell) (events : List MemoryAccess)
    (before after : Reference.RiscV.Sail.State) (edge : MemoryToken p × MemoryToken p) : Prop :=
  ∃ cell ∈ cells, ∃ earlier middle later newer,
    events = newer ++ transferEvent edge :: earlier ∧
    SailHistory cells earlier before middle ∧
    cell.addressCode = edge.1.address ∧
    cell.read middle = .ok edge.1.word.toBitVec middle ∧
    Reference.Sail.run (cell.write edge.2.word.toBitVec) middle = .ok () later ∧
    SailHistory cells newer later after

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
    (Reference.RiscV.Sail.FlatMemoryConfiguration before →
      Reference.RiscV.Sail.FlatMemoryConfiguration after) ∧
    ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
      cell.read after = .ok (memoryWord token.value) after

end Airbender.Delegation
