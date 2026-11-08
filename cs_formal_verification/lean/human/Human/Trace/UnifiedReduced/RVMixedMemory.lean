import Human.Helpers.UnifiedReduced.RVWindows
import Human.Trace.Delegation.RVExecution
import Human.Trace.Delegation.RVRequestHashWindows

/-! RV siblings of `MixedMemory.lean` and `SharedSpans.lean` (unified callers): the shared unified/caller/worker
    architecture executed as RV cell reads/writes (`RVHistory`) from a public `RV.State`. A RAM cell is RAM at any
    address, INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- RV sibling of `MixedMemoryEffects`: actual unified/worker transport through one initialized RV history. Native
    words, addresses and x0 values are derived; issued workers have actual RV call boundaries; from a nonzero initial
    clock every instruction has derived RV cycle states. -/
structure RVMixedMemoryEffects [Fact p.Prime] (data : RVRequestTrace p)
    (before : RV.State) (cells : List Cell) : Prop where
  requests : RVRequestBinding data before
  zeroReads : ∀ edge ∈ data.mixedSteps, edge.1.address = (Cell.register 0).addressCode → edge.1.value = 0
  words : ∀ edge ∈ data.mixedSteps, edge.1.word.Bounded ∧ edge.2.word.Bounded
  terminal : ∀ token ∈ data.machine.terminalMemory, token.word.Bounded
  addresses : ∀ edge ∈ data.mixedSteps, ∃ cell ∈ cells,
    cell.addressCode = edge.1.address ∧ cell.addressWord.Bounded
  operations : ∀ row ∈ data.workers.rows, Delegation.Caller.WorkerEffect row
  execution : ∃ (events : List MemoryAccess) (after : RV.State),
    events.Perm (data.mixedSteps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧
    RVHistory cells events before after ∧
    (∀ worker ∈ data.workers.rows, Delegation.Requests.Live (Delegation.Requests.fulfillment worker) →
      Delegation.RVCallExecution cells events before after worker) ∧
    (0 < (timeOfPair data.machine.initial.timestamp).value →
      ∀ row ∈ data.machine.rows, RVCycleExecution data cells events before after row) ∧
    ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
      cell.addressCode = token.address ∧ cell.readRV after = some token.word.toBitVec

/-- RV sibling of `SharedSpanInputs` (unified): public RV inputs for a complete hash span in the unified caller pool. -/
structure RVSharedSpanInputs [Fact p.Prime] (data : RVRequestTrace p)
    (before : RV.State) (addresses : List (BitVec 32)) (cells : List Cell)
    (span : Delegation.Caller.HashSpan) : Prop extends
      RVRequestInputs data before addresses,
      Delegation.Caller.HashSpan.RVProtocol data.workers before span where
  initialization : initialImageRV before cells = some data.machine.initialMemory
  distinct : (cells.map Cell.addressCode).Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned

/-- RV sibling of `SharedTerminalState` (unified): every terminal token is read from the same final RV state. -/
def RVSharedTerminalState [Fact p.Prime] (data : RVRequestTrace p) (after : RV.State)
    (cells : List Cell) : Prop :=
  ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
    cell.addressCode = token.address ∧ cell.readRV after = some token.word.toBitVec

/-- RV sibling of `SharedSpanEffects` (unified): decoded requests and the complete RV hash reference (with the delegate
    link) reach one actual shared terminal RV state. -/
structure RVSharedSpanEffects [Fact p.Prime] (data : RVRequestTrace p) (before : RV.State)
    (cells : List Cell) (span : Delegation.Caller.HashSpan) : Prop where
  requests : RVRequestBinding data before
  result : ∃ after, RVSharedTerminalState data after cells ∧
    Delegation.Caller.HashSpan.RVResult span data.workerProjection before after (Delegation.Caller.workerCells cells)

end Airbender.UnifiedReduced.Caller
