import Human.Trace.UnifiedReduced.MixedWindows
import Human.Helpers.UnifiedReduced.ControlPreparation

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

/-- Two public preparations share their actual cut states and the complete
    intervening machine/worker history. Raw control-write clocks survive both cuts. -/
def PreparedControlWindow [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (lower upper : Nat) (firstRegister : BitVec 5) (firstLiteral : ControlLiteral)
    (lastRegister : BitVec 5) (lastLiteral : ControlLiteral) : Prop :=
  ∃ (start finish : List (MemoryToken p)) (earlierEvents windowEvents : List MemoryAccess)
    (atStart atFinish : State),
    earlierEvents.Perm ((data.prefixSteps lower).map transferEvent) ∧
    windowEvents.Perm ((data.windowSteps lower upper).map transferEvent) ∧
    SailHistory cells earlierEvents before atStart ∧ SailHistory cells windowEvents atStart atFinish ∧
    NativeBoundary start atStart cells ∧ NativeBoundary finish atFinish cells ∧
    PreparedControl start atStart lower firstRegister firstLiteral ∧
    PreparedControl finish atFinish upper lastRegister lastLiteral

end Airbender.UnifiedReduced.Caller
