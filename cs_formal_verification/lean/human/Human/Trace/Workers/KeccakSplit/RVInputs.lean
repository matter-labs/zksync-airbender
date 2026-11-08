module
public import Human.Helpers.Memory.InitialImageRV
public import Human.Circuits.KeccakSplit.Native
public import Human.Helpers.Delegation.WorkerContext

@[expose] public section

/-! RV siblings of the split worker inputs (`Inputs.lean`): the public starting point is an `RV.State`; RAM cells are
    RAM at any address, INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/

namespace Airbender.Keccak.Split.Native
open Trace

/-- RV sibling of `MemoryInputs`: public initialization reads `RV.State` cells, one seed per address; the clock room
    and the approved invocation-high bound (`MemoryInputs.invocationHigh`) are unchanged. -/
structure RVMemoryInputs (data : MemoryData p) (before : RV.State) (cells : List Cell) : Prop where
  initialization : initialImageRV before cells = some data.initial
  distinct : (cells.map Cell.addressCode).Nodup
  clockRoom : ∀ row ∈ data.rows,
    (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase
  invocationHigh : ∀ row ∈ data.rows,
    (decodeTimestamp row.assignment row.columns.invocation).hi < timestampBase

/-- RV sibling of `OperationInputs`. -/
structure RVOperationInputs (data : MemoryData p) (before : RV.State) (cells : List Cell) : Prop where
  memory : RVMemoryInputs data before cells
  active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1

/-- RV sibling of `CallInputs`: one uninterrupted split Keccak-f[1600] request of 361 calls from x10 = 0. -/
structure RVCallInputs (data : MemoryData p) (initial : RV.State) (cells : List Cell) : Prop where
  memory : RVMemoryInputs data initial cells
  controlCell : Cell.register 10 ∈ cells
  controlStart : (Cell.register 10).readRV initial = some 0
  active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1
  calls : data.rows.length = 361

end Airbender.Keccak.Split.Native
