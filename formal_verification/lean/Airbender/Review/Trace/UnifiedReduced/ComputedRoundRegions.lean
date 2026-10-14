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

/-- A complete selected reference with either public preparation source.
    Global round masks are derived separately from prepared controller regions. -/
structure ComputedProtocolWindowInputs [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (window : HashWindow) : Prop where
  family : ∀ row ∈ data.workers.windowRows window.lower window.upper, row.family = window.span.family
  preparation : HashControlPreparation data program window.lower window.span
  calls : (data.workers.windowRows window.lower window.upper).length = window.span.callCount
  duration : window.upper = window.lower + 4 * window.span.callCount
  beforeTerminal : window.upper ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- Source-aware controller shape is derived from public modular regions.
    Full round-worker coverage remains the explicit global matching boundary. -/
structure WrappedProgramComputedPreparedProtocolInputs [Fact p.Prime] (data : RequestTrace p) (before : State)
    (ca oa : List (BitVec 32)) (cells : List Cell) (program : List UnifiedReduced.ProgramEntry)
    (regions : List RoundRegion) : Prop extends ProtocolContextInputs data before ca oa cells program where
  registry : WrappedSequentialProgram program
  scopes : ∀ region ∈ regions, WrappedProgramComputedRoundRegionInputs data program region
  coverage : ∀ row ∈ data.workers.rows, row.family = .blakeRound →
    ∃ region ∈ regions, row ∈ data.workers.windowRows region.lower region.upper

/-- Public modular code and reference duration derive the selected caller/worker
    shape for G, extended BLAKE or Keccak, with either preparation source. -/
structure WrappedProgramComputedProtocolWindowInputs [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (window : HashWindow) : Prop where
  region : WrappedProgramCallerRegion data program window.span.family window.lower window.upper
  preparation : HashControlPreparation data program window.lower window.span
  duration : window.upper = window.lower + 4 * window.span.callCount
  beforeTerminal : window.upper ≤ (timeOfPair data.machine.terminal.timestamp).value

end Airbender.UnifiedReduced.Caller
