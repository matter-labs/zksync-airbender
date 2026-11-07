import Airbender.Proofs.FullUnsigned.CallHistory
import Airbender.Proofs.Keccak.SplitNativeInputObservations

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Each actual split caller executes the original native memory call at
its shared-history boundaries, when supported public arguments hold there.
The common history supplies every raw bound and native input observation. -/
theorem unrolled_full_split_memory_call
    {initial origin finalState : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (fixedEquations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached Keccak.Split.Native.Proofs.fixedSetup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (row : Trace.Row babyBearModulus PooledFamily) (member : row ∈ trace.rows)
    (family : row.family = .addSub) (selected : Delegation.Requests.Selected row.assignment)
    (worker : Keccak.Split.Native.Row babyBearModulus) (present : worker ∈ splitWorkers.rows)
    (matched : worker.fulfillment splitWorkers.cached = Delegation.Requests.caller row.assignment)
    {cells : List Cell} {events : List MemoryAccess}
    (permutation : events.Perm ((unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events origin finalState)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (readable : ∀ cell ∈ cells, ∃ value, cell.read origin = .ok value origin)
    (reads : ∀ edge ∈ (unrolledFullMemoryData trace workers splitWorkers).steps, edge.1.word.Bounded) :
    let low := (decodeTimestamp row.assignment row.columns.initialTime).value
    ∃ before after,
      SailHistory cells (events.filter fun event => decide (event.1 ≤ low)) origin before ∧
      (∀ index : Fin 361, Keccak.Split.ArgumentsAt index.val before →
        Keccak.Split.Call.Executes worker.kind before after) ∧
      SailHistory cells (events.filter fun event => decide (low + 4 < event.1)) after finalState := by
  obtain ⟨before, after, past, localHistory, localEvents, future⟩ :=
    unrolled_full_split_caller_history setup lookup accepted excluded initialPC equations active
      initialClock initialAligned row member family selected worker present matched permutation ordered history
  have boundedReads : ∀ port ∈ worker.ports splitWorkers.cached,
      (readToken worker.assignment port).word.Bounded := by
    intro port physical
    have inWorkers : (readToken worker.assignment port, worker.writeToken splitWorkers.cached port) ∈
        splitWorkers.steps :=
      List.mem_flatMap.mpr ⟨worker, present, List.mem_map.mpr ⟨port, by simpa using physical, rfl⟩⟩
    exact reads _ (List.mem_append.mpr (Or.inr inWorkers))
  have atCall := history_cells_readable past aligned readable
  refine ⟨before, after, past, ?_, future⟩
  intro index arguments
  exact Keccak.Split.Native.Proofs.native_call_executes_of_history splitWorkers.cached worker
    (fixedEquations.rowsHold worker present) (active worker present) index arguments boundedReads
    localHistory localEvents aligned atCall

end Airbender.Compiler.MachineTargets.Proofs
