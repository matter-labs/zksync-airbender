import Airbender.Review.Trace.Delegation.HashWindows

namespace Airbender.Blake2Round
open Trace Reference.RiscV.Sail

/-- The first complete seven/ten-round span within one initialized ten-position
    controller. Later rows may remain outside the selected window. -/
structure WindowInputs [Fact p.Prime] (data : Delegation.MemoryData p) (before : State)
    (cells : List Cell) (flags : Fin 8) (lower upper : Nat) : Prop where
  memory : Delegation.BoundaryMemoryInputs data before cells
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeRound
  /-- The public flags initialize round zero. -/
  controlStart : (Cell.register 12).read before =
    .ok (BitVec.ofNat 32 ((8 + flags.val) * 65536)) before
  /-- The first cut precedes every native worker write. -/
  prefixEmpty : data.prefixRows lower = []
  /-- This pool stays within the controller's ten distinct round positions. -/
  roundsBound : data.rows.length ≤ 10
  /-- The unchanged complete-span ABI selects seven or ten native rows. -/
  calls : (data.windowRows lower upper).length = if flags.val % 2 = 1 then 7 else 10

end Airbender.Blake2Round
