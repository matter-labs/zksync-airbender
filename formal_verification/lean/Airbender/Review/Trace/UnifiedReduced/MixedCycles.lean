import Airbender.Review.Helpers.UnifiedReduced.RetirementProfile
import Airbender.Review.Trace.UnifiedReduced.CallerCycles
import Airbender.Review.Trace.UnifiedReduced.UnissuedWorkers

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Original Sail retirement for an ordinary row of the actual shared native
    path. Instruction identity is recovered from the public registry. -/
def OrdinaryCycle [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (program : List UnifiedReduced.ProgramEntry) (cells : List Cell)
    (events : List MemoryAccess) (initial finalState : State)
    (row : Trace.Row p UnifiedFamily) : Prop :=
  ∃ entry ∈ program, row.decoderQuery = entry.query ∧
    ∃ clause, Mixed.clauseFor entry.instruction = some clause ∧
      RetiresCycle cells events initial finalState row clause

/-- One initialized history and one complete native PC/clock path contain every
    ordinary instruction, caller and worker. Ordinary rows retire original Sail
    clauses; callers retain exactly `CallerCycle` observations and PC ticking.
    This is not `Realizes` for the full custom-CSR reference: invalid bigint
    controls and unissued prefix effects remain admitted. The final retired view
    binds the path's terminal PC and all actual terminal cells. -/
structure MixedCycleEffects [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    [Fact p.Prime] (data : RequestTrace p) (program : List UnifiedReduced.ProgramEntry)
    (initial : State) (cells : List Cell) : Prop where
  requests : RequestBinding data initial
  /-- All native machine transitions occur once between the raw public endpoints. -/
  path : ∃ states, StatePath data.machine states
  /-- Every conclusion below uses the same actual architectural history. -/
  execution : ∃ events finalState,
    events.Perm (data.mixedSteps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧ SailHistory cells events initial finalState ∧
    CurrentFetch data program initial cells events ∧
    (∀ row ∈ data.machine.rows, row ∉ data.callers →
      OrdinaryCycle program cells events initial finalState row) ∧
    (∀ row ∈ data.callers, CallerCycle data initial finalState cells events row) ∧
    (∀ worker ∈ data.workers.rows, Delegation.CallExecution cells events initial finalState worker ∧
      ((Delegation.Requests.fulfillment worker).time = (0, 0) →
        UnissuedPrefixExecution cells events initial finalState worker)) ∧
    let terminal := retiredState finalState data.machine.terminal.word.toBitVec
    Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) terminal =
      .ok data.machine.terminal.word.toBitVec terminal ∧
    ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
      cell.addressCode = token.address ∧ cell.read terminal = .ok token.word.toBitVec terminal

end Airbender.UnifiedReduced.Caller
