import Human.Helpers.UnifiedReduced.MixedMemory
import Human.Trace.UnifiedReduced.MixedExecution
import Human.Trace.Delegation.Execution

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- An original instruction retires between its actual cycle states in the
    shared history. The three windows retain earlier and later machine/worker
    effects. The clause is original Sail execution, not an expected output. -/
def RetiresCycle (cells : List Cell) (events : List MemoryAccess)
    (initial finalState : Reference.RiscV.Sail.State) (row : Trace.Row p UnifiedFamily)
    (clause : SailRV32.SailM SailRV32.ExecutionResult) : Prop :=
  ∃ before after,
    Trace.SailHistory cells (events.filter fun event => decide
      (event.1 ≤ (timeOfPair row.start.timestamp).value)) initial before ∧
    Trace.SailHistory cells (events.filter fun event => decide
      ((timeOfPair row.start.timestamp).value < event.1 ∧
        event.1 ≤ (timeOfPair row.finish.timestamp).value)) before after ∧
    Trace.SailHistory cells (events.filter fun event => decide
      ((timeOfPair row.finish.timestamp).value < event.1)) after finalState ∧
    Reference.Sail.run (Reference.RiscV.Sail.normalStep clause)
      (Trace.retiredState before row.start.word.toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (Trace.retiredState after row.finish.word.toBitVec)

/-- Actual unified/worker transport through one initialized history. This derives
    every native read/write/terminal word bound and architectural x0 value, then
    realizes the pool in Sail and reuses existing worker operation references.
    Issued workers have actual call boundaries inside that same history.
    Whole instruction retirement, ROM shadows and hash-span segmentation remain separate. -/
structure MixedMemoryEffects [Fact p.Prime] (data : RequestTrace p)
    (before : Reference.RiscV.Sail.State) (cells : List Cell) : Prop where
  /-- Public decoding and native requests identify each issued worker and its cycle. -/
  requests : RequestBinding data before
  /-- Architectural x0 reads are canonical zero, derived from initialization and writes. -/
  zeroReads : ∀ edge ∈ data.mixedSteps, edge.1.address = (Cell.register 0).addressCode → edge.1.value = 0
  /-- All unified/caller/worker reads and writes have sixteen-bit limbs. -/
  words : ∀ edge ∈ data.mixedSteps, edge.1.word.Bounded ∧ edge.2.word.Bounded
  /-- Every shared terminal word is canonical as well. -/
  terminal : ∀ token ∈ data.machine.terminalMemory, token.word.Bounded
  /-- Every native address selects an actually initialized canonical Sail cell. -/
  addresses : ∀ edge ∈ data.mixedSteps, ∃ cell ∈ cells,
    cell.addressCode = edge.1.address ∧ cell.addressWord.Bounded
  /-- Existing bigint/Clean hash references use these same actual native reads. -/
  operations : ∀ row ∈ data.workers.rows, Delegation.Caller.WorkerEffect row
  /-- Each transfer executes once in native time order and reaches all terminal cells.
      Every issued worker reads/writes one actual call pre/post-state inside this
      same history. From a nonzero public initial clock, every instruction also
      has derived cycle states containing its architectural and issued-worker ports.
      Native boot starts at clock four; surplus zero-clock workers stay exposed
      outside the issued-cycle guarantee. -/
  execution : ∃ (events : List MemoryAccess) (after : Reference.RiscV.Sail.State),
    events.Perm (data.mixedSteps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧
    Trace.SailHistory cells events before after ∧
    (∀ worker ∈ data.workers.rows, Delegation.Requests.Live (Delegation.Requests.fulfillment worker) →
      Delegation.CallExecution cells events before after worker) ∧
    (0 < (timeOfPair data.machine.initial.timestamp).value →
      ∀ row ∈ data.machine.rows, CycleExecution data cells events before after row) ∧
    ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
      cell.addressCode = token.address ∧ cell.read after = .ok token.word.toBitVec after

end Airbender.UnifiedReduced.Caller
