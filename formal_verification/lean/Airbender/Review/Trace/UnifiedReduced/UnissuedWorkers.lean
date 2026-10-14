import Airbender.Review.Trace.UnifiedReduced.MixedMemory
import Airbender.Review.Circuits.Blake2Round.Memory

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic Reference.RiscV.Sail

/-- Each native read is the full original public seed token, including its zero
    timestamp and canonical word. No operand value or supported mask is supplied. -/
def InitialWorkerReads (before : State) (cells : List Cell) (worker : Delegation.Row p) : Prop :=
  ∀ port ∈ worker.ports, ∃ cell ∈ cells, ∃ value,
    cell.read before = .ok value before ∧ readToken worker.assignment port = cell.initialToken value

/-- The actual public x12 seed determines exactly which exclusive round masks
    an unissued worker can have. This classifies controls; it does not assume one
    is supported or exclude a zero-clock worker. -/
def InitialRoundControl (before : State) (worker : Delegation.Row p) : Prop :=
  ∃ value, (Cell.register 12).read before = .ok value before ∧
    ∀ round : Fin 10, Blake2Round.Memory.RoundMask worker.assignment round ↔
      ∃ flags : Fin 8, (Word.ofBitVec value).hi = flags.val + 8 * 2 ^ round.val

/-- Architectural initialization and matching distinguish all worker invocation
    clocks, including zero. A single unissued worker can still have real effects. -/
structure WorkerInvocationUniqueness [Fact p.Prime] (data : RequestTrace p) : Prop where
  clocks : (data.workers.rows.map fun worker =>
    (timeOfPair (Delegation.Requests.fulfillment worker).time).value).Nodup
  raw : (data.workers.rows.map fun worker => (Delegation.Requests.fulfillment worker).time).Nodup
  unissued : (data.workers.rows.filter fun worker =>
    decide ((Delegation.Requests.fulfillment worker).time = (0, 0))).length ≤ 1

end Airbender.UnifiedReduced.Caller
