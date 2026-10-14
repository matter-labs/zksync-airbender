import Airbender.Review.Trace.UnifiedReduced.PreparedRoundWindows
import Airbender.Review.Helpers.UnifiedReduced.PCRelativePreparation

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Public instructions that prepare a protocol entry. AUIPC placement is a
    condition on decoded code addresses and immediates, not an assumed state
    value. Native matching identifies the actual final preparation instruction. -/
inductive HashControlPreparation [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (cut : Nat) (span : Delegation.Caller.HashSpan) : Prop where
  | literal (scope : ControlPreparation data program cut span.controlRegister (hashPreparation span))
  | pcRelative (immediate : BitVec 20)
      (scope : PCRelativePreparation data program cut span.controlRegister immediate)
      (placement : ∀ entry ∈ program, entry.pc = wrappedProgramAddress data (cut - 4) →
        entry.pc + (immediate ++ (0 : BitVec 12)) = span.controlStart)

/-- A complete selected G/Keccak span with literal or PC-relative public
    preparation. All existing domain, matching, table and protocol scope stays
    explicit. Earlier workers remain in the initialized history. -/
structure ComputedPreparedHashWindowInputs [Fact p.Prime] (data : RequestTrace p) (before : State)
    (ca oa : List (BitVec 32)) (cells : List Cell) (program : List UnifiedReduced.ProgramEntry)
    (span : Delegation.Caller.HashSpan) (lower upper : Nat) : Prop
    extends ProtocolContextInputs data before ca oa cells program where
  family : ∀ row ∈ data.workers.windowRows lower upper, row.family = span.family
  /-- Extended-round mask transport remains a separate entry. -/
  roundsAbsent : ∀ row ∈ data.workers.rows, row.family ≠ .blakeRound
  profile : span.family ≠ .blakeRound
  preparation : HashControlPreparation data program lower span
  calls : (data.workers.windowRows lower upper).length = span.callCount
  duration : upper = lower + 4 * span.callCount
  beforeTerminal : upper ≤ (timeOfPair data.machine.terminal.timestamp).value

end Airbender.UnifiedReduced.Caller
