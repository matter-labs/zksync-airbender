import Airbender.Review.Trace.UnifiedReduced.ControlPreparation
import Airbender.Review.Trace.UnifiedReduced.JointHashWindows

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Public instruction literals for the existing hash protocol entry controls. -/
def hashPreparation : Delegation.Caller.HashSpan → ControlLiteral
  | .blakeG reduced => .addi (if reduced then 128 else 0)
  | .blakeRound flags => .lui (BitVec.ofNat 20 ((8 + flags.val) * 16))
  | .keccak => .addi 0

/-- Public preparation and a complete hash span in a mixed architecture.
    G and Keccak need no supplied worker masks; extended BLAKE uses its separate
    prepared-round claim. No control read or worker boundary is an input. -/
structure PreparedHashWindowInputs [Fact p.Prime] (data : RequestTrace p) (before : State)
    (ca oa : List (BitVec 32)) (cells : List Cell) (program : List UnifiedReduced.ProgramEntry)
    (span : Delegation.Caller.HashSpan) (lower upper : Nat) : Prop where
  /-- Actual public CSR bytes and the initial native clock. -/
  publicProgram : RequestInputs data before ca
  /-- Original Sail decoding constructs the ordinary instruction registry. -/
  ordinaryProgram : Mixed.programImage before oa = some program
  /-- Successful public reads construct the joint architectural seed. -/
  initialization : initialImage before cells = some data.machine.initialMemory
  /-- Each physical cell is initialized once. -/
  distinct : (cells.map Cell.addressCode).Nodup
  /-- Tracked RAM words have the existing four-byte alignment. -/
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- The unified modeled setup uses the same public memory. -/
  setup : data.machine.rom = Setup.table before
  /-- Existing worker tables and the pinned modeled Keccak controller. -/
  tables : data.workers.setup = Delegation.modeledSetup Keccak.Controller.rows
  /-- Only selected workers belong to this uninterrupted hash protocol. -/
  family : ∀ row ∈ data.workers.windowRows lower upper, row.family = span.family
  /-- Other workers may be bigint, G or Keccak; round-mask transport is separate. -/
  roundsAbsent : ∀ row ∈ data.workers.rows, row.family ≠ .blakeRound
  /-- This prepared mixed-span claim admits G and Keccak. -/
  profile : span.family ≠ .blakeRound
  /-- Uniform or straight-path literal preparation; earlier workers remain in history. -/
  preparation : ControlPreparation data program lower span.controlRegister (hashPreparation span)
  /-- The complete span has the existing public protocol call count. -/
  calls : (data.workers.windowRows lower upper).length = span.callCount
  /-- Public duration; state/request matching derives every selected caller. -/
  duration : upper = lower + 4 * span.callCount
  /-- The final cut lies inside the native machine path. -/
  beforeTerminal : upper ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- Two complete prepared references use the same continuous native history,
    including all intervening preparation and other worker effects. -/
structure PreparedHashChainResult [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (firstSpan secondSpan : Delegation.Caller.HashSpan)
    (firstLower firstUpper secondLower secondUpper : Nat) : Prop where
  firstRequests : Delegation.Caller.RequestWindowBinding data.callers data.workers firstLower firstUpper
  secondRequests : Delegation.Caller.RequestWindowBinding data.callers data.workers secondLower secondUpper
  firstCount : (Delegation.Caller.windowCallers data.callers firstLower firstUpper).length = firstSpan.callCount
  secondCount : (Delegation.Caller.windowCallers data.callers secondLower secondUpper).length = secondSpan.callCount
  execution : ∃ chain : WindowChain p,
    chain.Realizes data before cells firstLower firstUpper secondLower secondUpper ∧
    firstSpan.Result (data.windowProjection firstLower firstUpper chain.firstStart chain.firstFinish)
      chain.atFirstStart chain.atFirstFinish (Delegation.Caller.workerCells cells) ∧
    secondSpan.Result (data.windowProjection secondLower secondUpper chain.secondStart chain.secondFinish)
      chain.atSecondStart chain.atSecondFinish (Delegation.Caller.workerCells cells)

end Airbender.UnifiedReduced.Caller
