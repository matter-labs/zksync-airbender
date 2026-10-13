import Airbender.Review.Trace.UnifiedReduced.MixedWindows
import Airbender.Review.Helpers.UnifiedReduced.ControlPreparation

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Public initialization and accepted ordinary writes reach an actual prepared
    cut state. This is control preparation and memory transport, not whole retirement. -/
def PreparedBoundaryExecution [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (cut : Nat) (register : BitVec 5) (literal : ControlLiteral) : Prop :=
  ∃ (tokens : List (MemoryToken p)) (events : List MemoryAccess) (atCut : State),
    events.Perm ((data.prefixSteps cut).map transferEvent) ∧
    SailHistory cells events before atCut ∧ NativeBoundary tokens atCut cells ∧
    PreparedControl tokens atCut cut register literal

end Airbender.UnifiedReduced.Caller
