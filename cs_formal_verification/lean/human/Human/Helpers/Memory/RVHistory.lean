module
public import Human.Helpers.Memory.RowEvents
public import Human.Helpers.Context.RVRowContext

@[expose] public section

namespace Airbender.Trace

/-- Actual RV reads and writes for a reverse-chronological Clean access list. The tail
    executes first. Reads do not change the state; writes do (`Cell.applyRV`; a RAM write is RAM at any address). -/
inductive RVHistory (cells : List Cell) : List MemoryAccess → RV.State → RV.State → Prop where
  | nil (before : RV.State) : RVHistory cells [] before before
  | cons {event : MemoryAccess} {rest before middle after}
      (past : RVHistory cells rest before middle)
      (cell : Cell) (member : cell ∈ cells) (address : cell.addressCode = event.2.1)
      (read : cell.readRV middle = some (memoryWord event.2.2.1))
      (write : cell.applyRV (memoryWord event.2.2.2) middle = some after) :
      RVHistory cells (event :: rest) before after

end Airbender.Trace
