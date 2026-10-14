import Airbender.Review.Trace.UnifiedReduced.MixedWindows
import Airbender.Review.Helpers.UnifiedReduced.RegisterDataflow

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic Reference.RiscV.Sail

/-- One initialized prefix reaches the actual tracked value, including gap
    writes and readonly refreshes. Exact prefix matching binds the boundary's
    canonical tokens to their actual native timestamps; a gap need not write
    this register at cut minus two. -/
def RegisterDataflowBoundaryExecution [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (cut : Nat) (register : BitVec 5) (value : BitVec 32) : Prop :=
  ∃ (tokens : List (MemoryToken p)) (events : List MemoryAccess) (atCut : State),
    events.Perm ((data.prefixSteps cut).map transferEvent) ∧
    SailHistory cells events before atCut ∧
    (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst) ∧
    NativeBoundary tokens atCut cells ∧
    (Cell.register register).read atCut = .ok value atCut ∧
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value

end Airbender.UnifiedReduced.Caller
