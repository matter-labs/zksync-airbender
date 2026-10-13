import Airbender.Review.Helpers.Delegation.MixedMemory

namespace Airbender.Delegation.Caller
open Trace

/-- Mixed architectural transport and worker operations on the actual native
    port values. Shared initialized history derives all ranges and x0 reads.
    This does not yet retire the mixed ISA trace or segment calls into hash
    spans; the flagged unissued zero-clock worker gap is still present. -/
structure MixedMemoryEffects [Fact p.Prime] (data : RequestTrace p)
    (before : Reference.RiscV.Sail.State) (cells : List Cell) : Prop where
  /-- Actual public callers identify their issued workers and native clocks. -/
  requests : RequestBinding data before
  /-- Canonical zero values are derived for every architectural x0 read. -/
  zeroReads : ∀ edge ∈ data.mixedSteps,
    edge.1.address = (Cell.register 0).addressCode → edge.1.value = 0
  /-- All machine/worker read and write words have sixteen-bit limbs. -/
  words : ∀ edge ∈ data.mixedSteps, edge.1.word.Bounded ∧ edge.2.word.Bounded
  /-- Native terminal words have the same canonical representation. -/
  terminal : ∀ token ∈ data.machine.terminalMemory, token.word.Bounded
  /-- Every native address selects a canonical initialized Sail cell. -/
  addresses : ∀ edge ∈ data.mixedSteps, ∃ cell ∈ cells,
    cell.addressCode = edge.1.address ∧ cell.addressWord.Bounded
  /-- Existing bigint/Clean hash references hold on actual worker port values. -/
  operations : ∀ row ∈ data.workers.rows, WorkerEffect row
  /-- Every architectural transfer executes once in native clock order and
      reaches all shared terminal cells in one actual Sail state. -/
  execution : ∃ (events : List MemoryAccess) (after : Reference.RiscV.Sail.State),
    events.Perm (data.mixedSteps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧
    Trace.SailHistory cells events before after ∧
    ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
      cell.addressCode = token.address ∧ cell.read after = .ok token.word.toBitVec after

end Airbender.Delegation.Caller
