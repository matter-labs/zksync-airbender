import Airbender.Review.Circuits.Bigint.Call
import Airbender.Review.Helpers.UnifiedReduced.MixedFetch

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Aggregate use of the existing temporary F02 contract at every actual bigint
    worker. This adds no operand, output, memory or desired-execution premise. -/
def BigintCommands [Fact p.Prime] (data : RequestTrace p) : Prop :=
  ∀ worker ∈ data.workers.rows, worker.family = .bigint →
    ∃ command, ExternalBoundary.BigintABI.Binding worker.assignment command

/-- Complete successful bigint reference call and PC retirement in this actual
    caller's shared-history window. Ordinary rows and other worker families keep
    their existing claims; this definition does not assert full hash-call closure. -/
def BigintCallCycle [Fact p.Prime] (data : RequestTrace p) (initial finalState : State)
    (domain : List Cell) (events : List MemoryAccess) (row : Trace.Row p UnifiedFamily) : Prop :=
  ∃ before after,
    SailHistory domain (events.filter fun event => decide (event.1 ≤ Delegation.Caller.startClock row)) initial before ∧
    SailHistory domain (events.filter fun event => decide
      (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)) before after ∧
    SailHistory domain (events.filter fun event => decide (Delegation.Caller.finishClock row < event.1)) after finalState ∧
    (∃ entry ∈ data.program, entry.data.family = .bigint ∧
      row.decoderQuery = Delegation.Caller.query entry ∧ row.start.word.toBitVec = entry.pc ∧
      entry.SourceWith (retiredState before row.start.word.toBitVec) Delegation.Caller.decoderFields) ∧
    Bigint.Call.Retires (retiredState before row.start.word.toBitVec) (retiredState after row.finish.word.toBitVec)

end Airbender.UnifiedReduced.Caller
