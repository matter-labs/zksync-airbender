import Airbender.Review.Trace.UnifiedReduced.MixedWindows
import Airbender.Review.Helpers.UnifiedReduced.RegisterPreparation

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- One initialized prefix reaches the actual ADDI operand state, then the
    selected native cycle reaches its prepared cut. Reads, values, selected row
    and retained output token are conclusions. This is memory preparation;
    complete Sail retirement and unrestricted public dataflow remain separate. -/
def RegisterImmediatePreparedBoundaryExecution [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (cut : Nat) (source register : BitVec 5) (immediate : BitVec 12) : Prop :=
  ∃ row ∈ data.machine.rows, Delegation.Caller.startClock row + 4 = cut ∧
    ∃ (tokens : List (MemoryToken p)) (events : List MemoryAccess) (atSource atCut : State),
      events.Perm ((data.prefixSteps (cut - 4)).map transferEvent) ∧
      SailHistory cells events before atSource ∧
      SailHistory cells (rowEvents 1 row).reverse atSource atCut ∧
      (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
        (tokens ++ (data.prefixSteps cut).map Prod.fst) ∧
      RegisterImmediatePreparedControl tokens atSource atCut cut source register immediate

end Airbender.UnifiedReduced.Caller
