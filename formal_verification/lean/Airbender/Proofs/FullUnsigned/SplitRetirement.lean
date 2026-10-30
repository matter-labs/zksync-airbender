import Airbender.Proofs.FullUnsigned.SplitPC
import Airbender.Proofs.Trace.Retirement

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private theorem split_arguments_retired {index : Nat} {before : State}
    (arguments : Keccak.Split.ArgumentsAt index before) (pc : BitVec 32) :
    Keccak.Split.ArgumentsAt index (retiredState before pc) := by
  obtain ⟨control, pointer, controlRead, pointerRead, value, lower, aligned⟩ := arguments
  exact ⟨control, pointer,
    cell_read_PC _ (cell_read_nextPC _ controlRead pc) pc,
    cell_read_PC _ (cell_read_nextPC _ pointerRead pc) pc, value, lower, aligned⟩

variable [Fact babyBearModulus.Prime]

/-- The actual split caller window realizes the original complete memory
call and Sail PC retirement. Public supported arguments remain explicit at
the extracted boundary. No native effect or retirement result is assumed. -/
theorem unrolled_full_split_caller_retirement
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
    (families : ∀ worker ∈ workers.rows, FullUnsigned.standardCall worker.family)
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
        Keccak.Split.Call.Retires worker.kind (retiredState before row.start.word.toBitVec)
          (retiredState after row.finish.word.toBitVec)) ∧
      SailHistory cells (events.filter fun event => decide (low + 4 < event.1)) after finalState := by
  obtain ⟨before, after, past, localHistory, localEvents, future⟩ :=
    unrolled_full_split_caller_history setup lookup accepted excluded initialPC equations active
      initialClock initialAligned row member family selected worker present matched permutation ordered history
  have atCall := history_cells_readable past aligned readable
  have prepared : ∀ cell ∈ cells, ∃ value,
      cell.read (retiredState before row.start.word.toBitVec) =
        .ok value (retiredState before row.start.word.toBitVec) := by
    intro cell included
    obtain ⟨value, read⟩ := atCall cell included
    exact ⟨value, cell_read_PC cell (cell_read_nextPC cell read _) _⟩
  have boundedReads : ∀ port ∈ worker.ports splitWorkers.cached,
      (readToken worker.assignment port).word.Bounded := by
    intro port physical
    have inWorkers : (readToken worker.assignment port, worker.writeToken splitWorkers.cached port) ∈
        splitWorkers.steps :=
      List.mem_flatMap.mpr ⟨worker, present, List.mem_map.mpr ⟨port, by simpa using physical, rfl⟩⟩
    exact reads _ (List.mem_append.mpr (Or.inr inWorkers))
  have pcBinding := unrolled_full_split_pc_binding setup lookup accepted excluded initialPC families equations
    active initialClock initialAligned row member family selected worker matched
  have start : Delegation.Caller.initialPC row.assignment = row.start.word := by
    cases row with | mk kind assignment => cases family; rfl
  have finish : Delegation.Caller.finalPC row.assignment = row.finish.word := by
    cases row with | mk kind assignment => cases family; rfl
  have retirement : run (do SailRV32.Functions.normal_base_next_pc (); SailRV32.Functions.tick_pc ())
      (retiredState after row.start.word.toBitVec) = .ok () (retiredState after row.finish.word.toBitVec) := by
    have actual : run (do SailRV32.Functions.normal_base_next_pc (); SailRV32.Functions.tick_pc ())
        (retiredState after row.start.word.toBitVec) =
          .ok () (retiredState (retiredState after row.start.word.toBitVec) row.finish.word.toBitVec) := by
      simpa only [finish, retiredState] using pcBinding.sail (retiredState after row.start.word.toBitVec)
        (by simpa only [start] using retired_state_pc after row.start.word.toBitVec)
    simpa only [retired_state_overwrite] using actual
  refine ⟨before, after, past, ?_, future⟩
  intro index arguments
  refine ⟨retiredState after row.start.word.toBitVec, ?_, retirement⟩
  exact Keccak.Split.Native.Proofs.native_call_executes_of_history splitWorkers.cached worker
    (fixedEquations.rowsHold worker present) (active worker present) index
    (split_arguments_retired arguments row.start.word.toBitVec) boundedReads
    (retired_state_history localHistory row.start.word.toBitVec) localEvents aligned prepared

end Airbender.Compiler.MachineTargets.Proofs
