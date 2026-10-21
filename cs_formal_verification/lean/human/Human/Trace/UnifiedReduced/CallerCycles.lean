import Human.Helpers.UnifiedReduced.MixedFetch
import Human.Trace.Delegation.RequestEffects

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Actual caller cycle boundaries, original public fetch, matched worker effects
    and Sail PC retirement. Bigint control validity and whole custom-CSR ABI remain separate. -/
def CallerCycle [Fact p.Prime] (data : RequestTrace p) (initial finalState : State)
    (cells : List Cell) (events : List MemoryAccess) (row : Trace.Row p UnifiedFamily) : Prop :=
  ∃ before after,
    SailHistory cells (events.filter fun event => decide (event.1 ≤ Delegation.Caller.startClock row)) initial before ∧
    SailHistory cells (events.filter fun event => decide
      (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)) before after ∧
    SailHistory cells (events.filter fun event => decide (Delegation.Caller.finishClock row < event.1)) after finalState ∧
    (∃ entry ∈ data.program, row.decoderQuery = Delegation.Caller.query entry ∧
      row.start.word.toBitVec = entry.pc ∧
      entry.SourceWith (retiredState before row.start.word.toBitVec) Delegation.Caller.decoderFields ∧
      ∃ worker ∈ data.workers.rows, Delegation.Requests.fulfillment worker = request row.assignment ∧
      worker.family = entry.data.family ∧ Delegation.Caller.WorkerEffect worker ∧
      ∀ port ∈ worker.ports, ∃ cell ∈ cells,
        cell.addressCode = port.address.code worker.assignment ∧
        cell.read (retiredState before row.start.word.toBitVec) =
          .ok (readToken worker.assignment port).word.toBitVec (retiredState before row.start.word.toBitVec) ∧
        cell.read (retiredState after row.finish.word.toBitVec) =
          .ok (worker.writeToken port).word.toBitVec (retiredState after row.finish.word.toBitVec)) ∧
    Reference.Sail.run (do Airbender.Reference.RiscV.Sail.normalBaseNextPC; SailRV32.Functions.tick_pc ())
      (retiredState after row.start.word.toBitVec) = .ok () (retiredState after row.finish.word.toBitVec)

/-- One shared initialized history supplies every caller cycle and terminal read.
    Zero-clock surplus effects remain in that history before issued cycles. -/
structure CallerCycleEffects [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (initial : State) (cells : List Cell) : Prop where
  /-- Original full-width requests and unique native worker slots. -/
  requests : RequestBinding data initial
  /-- Actual fetch, worker observations and PC retirement share the same states. -/
  execution : ∃ events finalState, events.Perm (data.mixedSteps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧ SailHistory cells events initial finalState ∧
    CurrentFetch data program initial cells events ∧
    (∀ row ∈ data.callers, CallerCycle data initial finalState cells events row) ∧
    ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
      cell.addressCode = token.address ∧ cell.read finalState = .ok token.word.toBitVec finalState

end Airbender.UnifiedReduced.Caller
