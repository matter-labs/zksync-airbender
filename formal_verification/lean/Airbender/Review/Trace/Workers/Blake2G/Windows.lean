import Airbender.Review.Trace.Delegation.HashWindows

namespace Airbender.Blake2G
open Trace Reference.RiscV.Sail

/-- One complete G-worker span selected after whole preceding spans.
    The public mode and request sizes fix the ABI; history supplies cut states. -/
structure WindowInputs [Fact p.Prime] (data : Delegation.MemoryData p) (before : State)
    (cells : List Cell) (reduced : Bool) (lower upper : Nat) : Prop where
  memory : Delegation.MemoryInputs data before cells
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeG
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  /-- The public mode initializes the first request's counter. -/
  controlStart : (Cell.register 12).read before = .ok (if reduced then 128 else 0) before
  /-- The prefix contains only complete requests of the same public mode. -/
  prefixComplete : (data.prefixRows lower).length % callCount reduced = 0
  /-- The selected window contains exactly one complete request. -/
  calls : (data.windowRows lower upper).length = callCount reduced

end Airbender.Blake2G
