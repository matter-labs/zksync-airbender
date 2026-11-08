module
public import Human.Trace.UnifiedReduced.RVControlPreparation
public import Human.Trace.UnifiedReduced.RVJointHashWindows
public import Human.Trace.UnifiedReduced.PreparedHashWindows

@[expose] public section

/-! RV siblings of the Sail-stated unified caller window contracts (same file name without `RV`): states are
    `RV.State`s, cells are read by `Cell.readRV` and executed by `RVHistory`, programs are RV program tables. A RAM cell
    is RAM at any address, INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- Public preparation and a complete hash span in a mixed architecture.
    G and Keccak need no supplied worker masks; extended BLAKE uses its separate
    prepared-round claim. No control read or worker boundary is an input. -/
structure RVPreparedHashWindowInputs [Fact p.Prime] (data : RVRequestTrace p) (before : RV.State)
    (ca oa : List (BitVec 32)) (cells : List Cell) (program : List UnifiedReduced.RVProgramEntry)
    (span : Delegation.Caller.HashSpan) (lower upper : Nat) : Prop where
  /-- Actual public CSR bytes and the initial native clock. -/
  publicProgram : RVRequestInputs data before ca
  /-- The RV ROM image and `RV.decode` construct the ordinary instruction registry. -/
  ordinaryProgram : rvProgramImageWith UnifiedReduced.rvDecoderFields before oa = some program
  /-- Successful public reads construct the joint architectural seed. -/
  initialization : initialImageRV before cells = some data.machine.initialMemory
  /-- Each physical cell is initialized once. -/
  distinct : (cells.map Cell.addressCode).Nodup
  /-- Tracked RAM words have the existing four-byte alignment. -/
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- The unified modeled setup uses the same public memory. -/
  setup : data.machine.rom = Setup.tableRV before
  /-- Existing worker tables and the pinned modeled Keccak controller. -/
  tables : data.workers.setup = Delegation.modeledSetup Keccak.Controller.rows
  /-- Only selected workers belong to this uninterrupted hash protocol. -/
  family : ∀ row ∈ data.workers.windowRows lower upper, row.family = span.family
  /-- Other workers may be bigint, G or Keccak; round-mask transport is separate. -/
  roundsAbsent : ∀ row ∈ data.workers.rows, row.family ≠ .blakeRound
  /-- This prepared mixed-span claim admits G and Keccak. -/
  profile : span.family ≠ .blakeRound
  /-- Uniform or straight-path literal preparation; earlier workers remain in history. -/
  preparation : RVControlPreparation data program lower span.controlRegister (hashPreparation span)
  /-- The complete span has the existing public protocol call count. -/
  calls : (data.workers.windowRows lower upper).length = span.callCount
  /-- Public duration; state/request matching derives every selected caller. -/
  duration : upper = lower + 4 * span.callCount
  /-- The final cut lies inside the native machine path. -/
  beforeTerminal : upper ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- Two complete prepared references use the same continuous native history,
    including all intervening preparation and other worker effects. -/
structure RVPreparedHashChainResult [Fact p.Prime] (data : RVRequestTrace p) (before : RV.State)
    (cells : List Cell) (firstSpan secondSpan : Delegation.Caller.HashSpan)
    (firstLower firstUpper secondLower secondUpper : Nat) : Prop where
  firstRequests : Delegation.Caller.RequestWindowBinding data.callers data.workers firstLower firstUpper
  secondRequests : Delegation.Caller.RequestWindowBinding data.callers data.workers secondLower secondUpper
  firstCount : (Delegation.Caller.windowCallers data.callers firstLower firstUpper).length = firstSpan.callCount
  secondCount : (Delegation.Caller.windowCallers data.callers secondLower secondUpper).length = secondSpan.callCount
  execution : ∃ chain : RVWindowChain p,
    chain.Realizes data before cells firstLower firstUpper secondLower secondUpper ∧
    Delegation.Caller.HashSpan.RVResult firstSpan (data.windowProjection firstLower firstUpper chain.firstStart chain.firstFinish)
      chain.atFirstStart chain.atFirstFinish (Delegation.Caller.workerCells cells) ∧
    Delegation.Caller.HashSpan.RVResult secondSpan (data.windowProjection secondLower secondUpper chain.secondStart chain.secondFinish)
      chain.atSecondStart chain.atSecondFinish (Delegation.Caller.workerCells cells)

/-- Request binding, exact caller count and the complete reference at one actual
    segment's states. It makes no whole custom-CSR retirement claim. -/
def RVHashWindowResult [Fact p.Prime] (data : RVRequestTrace p) (cells : List Cell)
    (window : HashWindow) (segment : RVWindowSegment p) : Prop :=
  Delegation.Caller.RequestWindowBinding data.callers data.workers window.lower window.upper ∧
  (Delegation.Caller.windowCallers data.callers window.lower window.upper).length = window.span.callCount ∧
  Delegation.Caller.HashSpan.RVResult window.span (data.windowProjection window.lower window.upper segment.start segment.finish)
    segment.atStart segment.atFinish (Delegation.Caller.workerCells cells)

/-- A nonempty list of complete prepared references uses one initialized history.
    Each intervening gap starts from the preceding segment's actual finish. -/
def RVPreparedHashSequenceResult [Fact p.Prime] (data : RVRequestTrace p) (before : RV.State)
    (cells : List Cell) (first : HashWindow) (rest : List HashWindow) : Prop :=
  ∃ sequence : RVWindowSequence p,
    sequence.Realizes data before cells first.lower ((first :: rest).map HashWindow.interval) ∧
    List.Forall₂ (RVHashWindowResult data cells) (first :: rest) sequence.segments

end Airbender.UnifiedReduced.Caller
