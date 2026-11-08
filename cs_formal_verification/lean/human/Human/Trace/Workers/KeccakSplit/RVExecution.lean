module
public import Human.Trace.Workers.KeccakSplit.RVInputs
public import Human.Helpers.Delegation.RVMemory

@[expose] public section

/-! RV siblings of the split memory execution and trace mapping (`Execution.lean`). RAM cells are RAM at any address,
    INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/

namespace Airbender.Keccak.Split.Native
open Trace

/-- RV sibling of `MemoryExecution`: every imported split-worker access executes once, in native timestamp order, as
    RV cell reads/writes (`RVHistory`) from the public initial state; untouched aligned cells keep their reads; every
    terminal token is read from the final state. -/
def RVMemoryExecution (data : MemoryData p) (before : RV.State) (cells : List Cell) : Prop :=
  ∃ (events : List MemoryAccess) (after : RV.State),
    events.Perm (data.steps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧
    RVHistory cells events before after ∧
    (∀ edge ∈ data.steps, Delegation.RVPortExecution cells events before after edge) ∧
    (∀ cell : Cell, cell.Aligned → (∀ edge ∈ data.steps, edge.1.address ≠ cell.addressCode) →
      ∀ value, cell.readRV before = some value → cell.readRV after = some value) ∧
    ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
      cell.readRV after = some (memoryWord token.value)

/-- RV sibling of `TraceMapping`. -/
structure RVTraceMapping (data : MemoryData p) (initial after : RV.State) (cells : List Cell) : Prop where
  history : ∃ events : List MemoryAccess, events.Perm (data.steps.map transferEvent) ∧
    RVHistory cells events initial after
  finalCells : ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
    cell.readRV after = some token.word.toBitVec

end Airbender.Keccak.Split.Native
