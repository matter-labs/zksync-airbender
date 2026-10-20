import Human.Trace.Workers.Keccak.Call
import Human.Helpers.Delegation.BoundaryMemory

namespace Airbender.Keccak
open Trace Reference.RiscV.Sail

/-- The existing complete Keccak ABI at a native memory boundary. Actual
    seed values come from `BoundaryImage`; their timestamps need not be zero. -/
structure NativeCallInputs [Fact p.Prime] (data : Delegation.MemoryData p)
    (initial : State) (cells : List Cell) : Prop where
  memory : Delegation.BoundaryMemoryInputs data initial cells
  /-- Public initial mode of the unchanged 649-call protocol. -/
  controlStart : (Cell.register 10).read initial = .ok 0 initial
  /-- This uninterrupted request contains active Keccak workers. -/
  family : ∀ row ∈ data.rows, row.family = .keccak
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  /-- The unchanged complete-span caller ABI. -/
  calls : data.rows.length = 649

end Airbender.Keccak
