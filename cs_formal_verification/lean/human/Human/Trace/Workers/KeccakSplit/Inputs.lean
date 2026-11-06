import Human.Circuits.KeccakSplit.Native
import Human.Helpers.Delegation.WorkerContext

namespace Airbender.Keccak.Split.Native
open Trace

/-- Public initialization reads actual Sail cells, with one seed per address;
    invocation clocks leave room for the offset-two writes. Previous-access ranges
    are proved internally. -/
structure MemoryInputs (data : MemoryData p) (before : Reference.RiscV.Sail.State)
    (cells : List Cell) : Prop where
  initialization : initialImage before cells = some data.initial
  distinct : (cells.map Cell.addressCode).Nodup
  clockRoom : ∀ row ∈ data.rows,
    (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase
  /-- Approved assumption, as for the other delegation workers
      (`Delegation.MemoryInputs.invocationHigh`): the split workers range-check only
      `(invocation-low - execute) / 4`, never the invocation high limb. Cross-circuit
      binding should discharge it: the invocation clock is the main circuit's
      range-checked delegation request clock. -/
  invocationHigh : ∀ row ∈ data.rows,
    (decodeTimestamp row.assignment row.columns.invocation).hi < timestampBase

/-- Inputs of a pool of split workers: initialized memory, and every supplied row
    is an active call (padding rows await request binding). -/
structure OperationInputs (data : MemoryData p) (before : Reference.RiscV.Sail.State)
    (cells : List Cell) : Prop where
  memory : MemoryInputs data before cells
  active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1

/-- One uninterrupted split Keccak-f[1600] request: the 361 calls of `schedule`,
    starting with control word zero in x10. Initialized matching proves every later
    control read, the call order and the state pointer; no per-call value is supplied.
    Connecting this span to the calling instructions remains the request-binding task. -/
structure CallInputs (data : MemoryData p) (initial : Reference.RiscV.Sail.State)
    (cells : List Cell) : Prop where
  memory : MemoryInputs data initial cells
  controlCell : Cell.register 10 ∈ cells
  controlStart : (Cell.register 10).read initial = .ok 0 initial
  active : ∀ row ∈ data.rows, row.assignment row.columns.execute = 1
  calls : data.rows.length = 361

end Airbender.Keccak.Split.Native
