import Airbender.Review.Delegation.Memory
import Airbender.Proofs.Trace.SailHistory

namespace Airbender.Delegation
open Trace Trace.Proofs

/-- Actual Sail cell execution of every imported delegation access, once each,
    from the public initial state. Events follow native timestamp order; ties
    are permitted because all delegation ports use the same clock slot.

    Every declared terminal token is read from the resulting Sail state.
    This connects the memory argument to registers/RAM; operation semantics,
    caller ABI and whole hash scheduling are separate claims. -/
def MemoryExecution (data : MemoryData p) (before : Reference.RiscV.Sail.State)
    (cells : List Cell) : Prop :=
  ∃ (events : List MemoryAccess) (after : Reference.RiscV.Sail.State),
    events.Perm (data.steps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧
    SailHistory cells events before after ∧
    ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
      cell.read after = .ok (memoryWord token.value) after

end Airbender.Delegation
