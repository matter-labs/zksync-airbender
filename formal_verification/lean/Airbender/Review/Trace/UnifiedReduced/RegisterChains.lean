import Airbender.Review.Trace.UnifiedReduced.MixedWindows
import Airbender.Review.Helpers.UnifiedReduced.RegisterChains

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic Reference.RiscV.Sail

/-- One initialized native prefix reaches the actual computed register value.
    The boundary token is canonical and retains its final write timestamp.
    This is memory preparation; complete instruction retirement is separate. -/
def RegisterChainPreparedBoundaryExecution [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (cut : Nat) (register : BitVec 5) (value : BitVec 32) : Prop :=
  ∃ (tokens : List (MemoryToken p)) (events : List MemoryAccess) (atCut : State),
    events.Perm ((data.prefixSteps cut).map transferEvent) ∧
    SailHistory cells events before atCut ∧ NativeBoundary tokens atCut cells ∧
    (Cell.register register).read atCut = .ok value atCut ∧
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧
      (timeOfPair token.time).value = cut - 2 ∧ token.word = Word.ofBitVec value

end Airbender.UnifiedReduced.Caller
