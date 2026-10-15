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

/-- The actual bigint return is a canonical bit at the instruction boundary.
    This includes unsupported incoming controls; no opcode validity or expected
    output is supplied. The return token retains its worker clock, cut minus one. -/
def BigintControlBoundaryExecution [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (cut : Nat) : Prop :=
  ∃ (tokens : List (MemoryToken p)) (events : List MemoryAccess) (atCut : State) (value : BitVec 32),
    events.Perm ((data.prefixSteps cut).map transferEvent) ∧
    SailHistory cells events before atCut ∧
    (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst) ∧
    NativeBoundary tokens atCut cells ∧ (value = 0 ∨ value = 1) ∧
    (Cell.register 12).read atCut = .ok value atCut ∧
    ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
      (timeOfPair token.time).value = cut - 1 ∧ token.word = Word.ofBitVec value

end Airbender.UnifiedReduced.Caller
