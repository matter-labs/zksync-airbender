module
public import Human.Helpers.Delegation.WorkerContext
public import Human.Helpers.Memory.RVHistory

@[expose] public section

/-! RV-typed siblings of the delegation memory inputs and execution relations (`Memory.lean`, `WorkerContext.lean`):
    the public starting point is an `RV.State`, cells are read by `Cell.readRV` and updated by `Cell.applyRV`
    (`RVHistory`). Same fields otherwise; no `Configured`. A RAM cell is RAM at any address, INCLUDING THE SHADOW RAM
    BELOW `ROM_END` (read-write for delegations, `RV.State.delegationRAM`); no pointer is required to be at or above
    `ROM_END`. -/

namespace Airbender.Delegation
open Trace

/-- RV sibling of `MemoryInputs`: public initialization reads `RV.State` cells, one seed per address; the clock-room
    and the approved invocation-high bound are unchanged. -/
structure RVMemoryInputs (data : MemoryData p) (before : RV.State) (cells : List Cell) : Prop where
  initialization : initialImageRV before cells = some data.initial
  distinct : (cells.map Cell.addressCode).Nodup
  clockRoom : ∀ row ∈ data.rows,
    (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase
  /-- The approved assumption of `MemoryInputs.invocationHigh` (cross-circuit binding discharges it later). -/
  invocationHigh : ∀ row ∈ data.rows,
    (decodeTimestamp row.assignment row.columns.invocation).hi < timestampBase

/-- RV sibling of `PortExecution`: one native port's read/write position in the shared RV history. -/
def RVPortExecution (cells : List Cell) (events : List MemoryAccess)
    (before after : RV.State) (edge : MemoryToken p × MemoryToken p) : Prop :=
  ∃ cell ∈ cells, ∃ earlier middle later newer,
    events = newer ++ transferEvent edge :: earlier ∧
    RVHistory cells earlier before middle ∧
    cell.addressCode = edge.1.address ∧
    cell.readRV middle = some edge.1.word.toBitVec ∧
    cell.applyRV edge.2.word.toBitVec middle = some later ∧
    RVHistory cells newer later after

/-- RV sibling of `CallExecution`: one complete worker call inside the shared RV history. -/
def RVCallExecution (cells : List Cell) (events : List MemoryAccess)
    (before after : RV.State) (row : Row p) : Prop :=
  ∃ earlier current newer start finish,
    events = newer ++ current ++ earlier ∧
    current.Perm (row.memorySteps.map transferEvent) ∧
    RVHistory cells earlier before start ∧
    RVHistory cells current start finish ∧
    RVHistory cells newer finish after ∧
    ∀ port ∈ row.ports, ∃ cell ∈ cells,
      cell.addressCode = port.address.code row.assignment ∧
      cell.readRV start = some (readToken row.assignment port).word.toBitVec ∧
      cell.readRV finish = some (row.writeToken port).word.toBitVec

end Airbender.Delegation
