module
public import Human.Trace.UnifiedReduced.RVMixedWindows
public import Human.Helpers.UnifiedReduced.RVControlPreparation

@[expose] public section

/-! Unified caller window contracts: states are
    `RV.State`s, cells are read by `Cell.readRV` and executed by `RVHistory`, programs are RV program tables. A RAM cell
    is RAM at any address, INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- Public initialization and accepted ordinary writes reach an actual prepared
    cut state. This is control preparation and memory transport, not whole retirement. -/
def RVPreparedBoundaryExecution [Fact p.Prime] (data : RVRequestTrace p) (before : RV.State)
    (cells : List Cell) (cut : Nat) (register : BitVec 5) (literal : ControlLiteral) : Prop :=
  ∃ (tokens : List (MemoryToken p)) (events : List MemoryAccess) (atCut : RV.State),
    events.Perm ((data.prefixSteps cut).map transferEvent) ∧
    RVHistory cells events before atCut ∧ RVNativeBoundary tokens atCut cells ∧
    RVPreparedControl tokens atCut cut register literal

/-- Two public preparations share their actual cut states and the complete
    intervening machine/worker history. Raw control-write clocks survive both cuts. -/
def RVPreparedControlWindow [Fact p.Prime] (data : RVRequestTrace p) (before : RV.State)
    (cells : List Cell) (lower upper : Nat) (firstRegister : BitVec 5) (firstLiteral : ControlLiteral)
    (lastRegister : BitVec 5) (lastLiteral : ControlLiteral) : Prop :=
  ∃ (start finish : List (MemoryToken p)) (earlierEvents windowEvents : List MemoryAccess)
    (atStart atFinish : RV.State),
    earlierEvents.Perm ((data.prefixSteps lower).map transferEvent) ∧
    windowEvents.Perm ((data.windowSteps lower upper).map transferEvent) ∧
    RVHistory cells earlierEvents before atStart ∧ RVHistory cells windowEvents atStart atFinish ∧
    RVNativeBoundary start atStart cells ∧ RVNativeBoundary finish atFinish cells ∧
    RVPreparedControl start atStart lower firstRegister firstLiteral ∧
    RVPreparedControl finish atFinish upper lastRegister lastLiteral

end Airbender.UnifiedReduced.Caller
