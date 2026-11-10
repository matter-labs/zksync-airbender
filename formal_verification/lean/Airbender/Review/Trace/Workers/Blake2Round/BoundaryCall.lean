import Airbender.Review.Trace.Workers.Blake2Round.Call
import Airbender.Review.Helpers.Delegation.BoundaryMemory

namespace Airbender.Blake2Round
open Trace Reference.RiscV.Sail

/-- The complete extended-BLAKE caller ABI at a native boundary, retaining seed clocks. -/
structure NativeCallInputs [Fact p.Prime] (data : Delegation.MemoryData p)
    (initial : State) (cells : List Cell) (flags : Fin 8) : Prop where
  memory : Delegation.BoundaryMemoryInputs data initial cells
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeRound
  /-- The public flags start round zero of the unchanged seven/ten-call protocol. -/
  controlStart : (Cell.register 12).read initial =
    .ok (BitVec.ofNat 32 ((8 + flags.val) * 65536)) initial
  calls : data.rows.length = if flags.val % 2 = 1 then 7 else 10

end Airbender.Blake2Round
