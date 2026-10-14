import Airbender.Review.Trace.UnifiedReduced.MixedWindows
import Airbender.Review.Helpers.UnifiedReduced.PCRelativePreparation

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Public AUIPC preparation reaches an actual cut state in the initialized
    mixed history, with its canonical value and original native write timestamp. -/
def PCRelativePreparedBoundaryExecution [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (cut : Nat) (register : BitVec 5) (immediate : BitVec 20) : Prop :=
  ∃ (tokens : List (MemoryToken p)) (events : List MemoryAccess) (atCut : State),
    events.Perm ((data.prefixSteps cut).map transferEvent) ∧
    SailHistory cells events before atCut ∧ NativeBoundary tokens atCut cells ∧
    PCRelativePreparedControl data tokens atCut cut register immediate

end Airbender.UnifiedReduced.Caller
