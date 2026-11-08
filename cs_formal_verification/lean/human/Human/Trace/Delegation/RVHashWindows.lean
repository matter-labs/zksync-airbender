module
public import Human.Helpers.Delegation.NativeWindows
public import Human.Helpers.Delegation.RVBoundaryMemory

@[expose] public section

namespace Airbender.Delegation.Caller
open Trace

/-- RV sibling of `HashSpan.WindowResult`, for a span result `result` over `RV.State`s (each worker family states its
    own, e.g. `Blake2G.RVSpanResult`): a complete span reaches `result` on the actual RV states of a native-clock
    window. Both states and all boundary reads are derived from the public initial history. RAM cells include
    READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/
def RVWindowResult [Fact p.Prime] (result : MemoryData p → RV.State → RV.State → List Cell → Prop)
    (data : MemoryData p) (before : RV.State) (cells : List Cell) (lower upper : Nat) : Prop :=
  ∃ (start finish : List (MemoryToken p)) (earlierEvents spanEvents : List MemoryAccess)
    (atStart atFinish : RV.State),
    earlierEvents.Perm ((data.prefixRows lower).flatMap Row.memorySteps |>.map transferEvent) ∧
    spanEvents.Perm ((data.windowRows lower upper).flatMap Row.memorySteps |>.map transferEvent) ∧
    RVHistory cells earlierEvents before atStart ∧ RVHistory cells spanEvents atStart atFinish ∧
    MemoryAccepted ⟨data.setup, data.windowRows lower upper, start, finish⟩ ∧
    RVBoundaryMemoryInputs ⟨data.setup, data.windowRows lower upper, start, finish⟩ atStart cells ∧
    result ⟨data.setup, data.windowRows lower upper, start, finish⟩ atStart atFinish cells

end Airbender.Delegation.Caller
