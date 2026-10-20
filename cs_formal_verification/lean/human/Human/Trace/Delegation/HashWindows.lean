import Human.Helpers.Delegation.NativeWindows
import Human.Helpers.Delegation.BoundaryMemory
import Human.Trace.Delegation.SharedSpans

namespace Airbender.Delegation.Caller
open Trace Reference.RiscV.Sail

/-- A complete hash reference on the actual states of a native-clock window.
    Both states and all boundary reads are derived from the public initial history. -/
def HashSpan.WindowResult [Fact p.Prime] (span : HashSpan) (data : MemoryData p)
    (before : State) (cells : List Cell) (lower upper : Nat) : Prop :=
  ∃ (start finish : List (MemoryToken p)) (earlierEvents spanEvents : List MemoryAccess)
    (atStart atFinish : State),
    earlierEvents.Perm ((data.prefixRows lower).flatMap Row.memorySteps |>.map transferEvent) ∧
    spanEvents.Perm ((data.windowRows lower upper).flatMap Row.memorySteps |>.map transferEvent) ∧
    SailHistory cells earlierEvents before atStart ∧ SailHistory cells spanEvents atStart atFinish ∧
    MemoryAccepted ⟨data.setup, data.windowRows lower upper, start, finish⟩ ∧
    BoundaryMemoryInputs ⟨data.setup, data.windowRows lower upper, start, finish⟩ atStart cells ∧
    span.Result ⟨data.setup, data.windowRows lower upper, start, finish⟩ atStart atFinish cells

end Airbender.Delegation.Caller
