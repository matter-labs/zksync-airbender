import Airbender.Review.Trace.UnifiedReduced.ComputedHashWindows

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- A controller region whose entry comes from literal or publicly placed AUIPC
    code. Raw matching derives its masks; no control read or mask is supplied. -/
structure ComputedRoundRegionInputs [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (region : RoundRegion) : Prop where
  family : ∀ row ∈ data.workers.windowRows region.lower region.upper, row.family = .blakeRound
  preparation : HashControlPreparation data program region.lower (.blakeRound region.flags)
  roundsBound : (data.workers.windowRows region.lower region.upper).length ≤ 10
  duration : region.upper = region.lower + 4 * (data.workers.windowRows region.lower region.upper).length
  aligned : region.lower % 4 = 0 ∧ region.upper % 4 = 0
  beforeTerminal : region.upper ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- Public modular code and at most forty ticks derive local controller shape
    before source-aware raw matching transports the actual round-zero seed. -/
structure WrappedProgramComputedRoundRegionInputs [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (region : RoundRegion) : Prop where
  code : WrappedProgramCallerRegion data program .blakeRound region.lower region.upper
  preparation : HashControlPreparation data program region.lower (.blakeRound region.flags)
  extent : region.lower ≤ region.upper ∧ region.upper ≤ region.lower + 4 * 10
  aligned : region.lower % 4 = 0 ∧ region.upper % 4 = 0
  beforeTerminal : region.upper ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- Global mask transport retains the existing explicit full round-worker
    coverage boundary. Local regions do not themselves exclude unissued workers. -/
structure ComputedPreparedProtocolInputs [Fact p.Prime] (data : RequestTrace p) (before : State)
    (ca oa : List (BitVec 32)) (cells : List Cell) (program : List UnifiedReduced.ProgramEntry)
    (regions : List RoundRegion) : Prop extends ProtocolContextInputs data before ca oa cells program where
  scopes : ∀ region ∈ regions, ComputedRoundRegionInputs data program region
  coverage : ∀ row ∈ data.workers.rows, row.family = .blakeRound →
    ∃ region ∈ regions, row ∈ data.workers.windowRows region.lower region.upper

end Airbender.UnifiedReduced.Caller
