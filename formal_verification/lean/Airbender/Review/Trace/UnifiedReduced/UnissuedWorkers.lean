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

/-- A zero-clock worker is the actual first transfer group. Its native reads
    observe the public initial state and its writes reach the actual prefix end;
    all later transfers remain in the same history. No caller is invented. -/
def UnissuedPrefixExecution (cells : List Cell) (events : List MemoryAccess)
    (before after : State) (worker : Delegation.Row p) : Prop :=
  ∃ current newer finish,
    events = newer ++ current ∧
    current.Perm (worker.memorySteps.map transferEvent) ∧
    SailHistory cells current before finish ∧
    SailHistory cells newer finish after ∧
    ∀ port ∈ worker.ports, ∃ cell ∈ cells,
      cell.addressCode = port.address.code worker.assignment ∧
      cell.read before = .ok (readToken worker.assignment port).word.toBitVec before ∧
      cell.read finish = .ok (worker.writeToken port).word.toBitVec finish

/-- All workers, including the possible unissued worker, have actual call states
    in one initialized architectural execution reaching the shared terminal cells.
    This is transfer execution, separate from caller retirement or control ABI. -/
def MixedWorkerExecution [Fact p.Prime] (data : RequestTrace p)
    (before : State) (cells : List Cell) : Prop :=
  ∃ (events : List MemoryAccess) (after : State),
    events.Perm (data.mixedSteps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧
    SailHistory cells events before after ∧
    (∀ worker ∈ data.workers.rows, Delegation.CallExecution cells events before after worker) ∧
    (∀ worker ∈ data.workers.rows, (Delegation.Requests.fulfillment worker).time = (0, 0) →
      UnissuedPrefixExecution cells events before after worker) ∧
    ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
      cell.addressCode = token.address ∧ cell.read after = .ok token.word.toBitVec after

end Airbender.UnifiedReduced.Caller
