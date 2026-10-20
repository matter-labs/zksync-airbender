import Human.Trace.Workers.Blake2G.Call
import Human.Helpers.Delegation.BoundaryMemory

namespace Airbender.Blake2G
open Trace Reference.RiscV.Sail

/-- The complete G caller ABI at a native boundary, retaining seed clocks. -/
structure NativeCallInputs [Fact p.Prime] (data : Delegation.MemoryData p)
    (initial : State) (cells : List Cell) (reduced : Bool) : Prop where
  memory : Delegation.BoundaryMemoryInputs data initial cells
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeG
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  /-- The public mode starts the unchanged 56/80-call counter. -/
  controlStart : (Cell.register 12).read initial =
    .ok (if reduced then 128 else 0) initial
  calls : data.rows.length = callCount reduced

end Airbender.Blake2G
