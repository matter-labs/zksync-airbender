import Airbender.Review.Trace.Delegation.HashWindows

namespace Airbender.Keccak
open Trace Reference.RiscV.Sail

/-- The first complete Keccak span in a native worker pool. Later workers may
    remain outside the selected window; history derives both cut states. -/
structure WindowInputs [Fact p.Prime] (data : Delegation.MemoryData p) (before : State)
    (cells : List Cell) (lower upper : Nat) : Prop where
  memory : Delegation.BoundaryMemoryInputs data before cells
  tables : data.setup = Delegation.modeledSetup Controller.rows
  family : ∀ row ∈ data.rows, row.family = .keccak
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  /-- The public initial mode of the existing Keccak protocol. -/
  controlStart : (Cell.register 10).read before = .ok 0 before
  /-- The first cut precedes every native worker write. -/
  prefixEmpty : data.prefixRows lower = []
  /-- The unchanged complete-span ABI selects exactly 649 workers. -/
  calls : (data.windowRows lower upper).length = 649

end Airbender.Keccak
