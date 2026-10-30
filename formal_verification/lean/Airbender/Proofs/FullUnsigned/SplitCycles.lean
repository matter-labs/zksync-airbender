import Airbender.Proofs.FullUnsigned.SplitRetirement
import Airbender.Proofs.Trace.CycleComposition
import Airbender.Proofs.Trace.TransferBoundary

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private theorem split_prepared_arguments {index : Nat} {state : State}
    (arguments : Keccak.Split.ArgumentsAt index state) (pc : BitVec 32) :
    Keccak.Split.ArgumentsAt index (retiredState state pc) := by
  obtain ⟨control, pointer, readControl, readPointer, selected, outside, aligned⟩ := arguments
  exact ⟨control, pointer,
    cell_read_PC (Cell.register 10) (cell_read_nextPC (Cell.register 10) readControl pc) pc,
    cell_read_PC (Cell.register 11) (cell_read_nextPC (Cell.register 11) readPointer pc) pc,
    selected, outside, aligned⟩

variable [Fact babyBearModulus.Prime]

/-- Each split caller has its actual public source and full history window.
At those cuts, supported arguments imply complete native memory execution and
original Sail retirement. Both cache modes use every actual worker port. -/
theorem unrolled_full_split_caller_cycle
    {initial finalState : State} {text : List (BitVec 32)} {capacity : Nat}
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
    {cells : List Cell}
    (inputs : Transfer.NativeInputs (unrolledFullMemoryData trace workers splitWorkers) initial cells)
    (reads : ∀ edge ∈ (unrolledFullMemoryData trace workers splitWorkers).steps, edge.1.word.Bounded)
    (row : Trace.Row babyBearModulus PooledFamily) (member : row ∈ trace.rows)
    (family : row.family = .addSub) (selected : Delegation.Requests.Selected row.assignment)
    (worker : Keccak.Split.Native.Row babyBearModulus) (present : worker ∈ splitWorkers.rows)
    (matched : worker.fulfillment splitWorkers.cached = Delegation.Requests.caller row.assignment)
    {events : List MemoryAccess}
    (permutation : events.Perm ((unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (readonly : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ before after,
      SailHistory cells (events.filter fun event => decide
        (event.1 ≤ (timeOfPair row.start.timestamp).value)) initial before ∧
      SailHistory cells (events.filter fun event => decide
        ((timeOfPair row.start.timestamp).value < event.1 ∧
          event.1 ≤ (timeOfPair row.finish.timestamp).value)) before after ∧
      SailHistory cells (events.filter fun event => decide
        ((timeOfPair row.finish.timestamp).value < event.1)) after finalState ∧
      ∃ entry ∈ FullUnsigned.entriesWith Keccak.Split.Caller.decoderFields text,
        entry.SourceWith before Keccak.Split.Caller.decoderFields ∧
        row.start.word.toBitVec = entry.pc ∧
        Delegation.Caller.nativeQuery row.assignment = Keccak.Split.Caller.query entry ∧
        worker.kind = entry.data.family ∧
        ∀ index : Fin 361, Keccak.Split.ArgumentsAt index.val before →
          Keccak.Split.Call.Executes worker.kind before after ∧
          Keccak.Split.Call.Retires worker.kind (retiredState before row.start.word.toBitVec)
            (retiredState after row.finish.word.toBitVec) := by
  obtain ⟨before, after, past, localHistory, localEvents, future⟩ :=
    unrolled_full_split_caller_history setup lookup accepted excluded initialPC equations active
      initialClock initialAligned row member family selected worker present matched permutation ordered history
  let low := row.clock
  obtain ⟨cutBefore, cutAfter, _, cutPast, current, _⟩ :=
    history_window ordered history (by omega : low ≤ low + 4)
  have sameBefore := sail_history_deterministic past cutPast
  subst cutBefore
  have sameAfter := sail_history_deterministic localHistory (history_without_zero current)
  subst cutAfter
  have readable := history_cells_readable past aligned (by
    intro cell included
    obtain ⟨_, _, _, read, _⟩ := Transfer.native_cell_source inputs included
    exact ⟨_, read⟩)
  have prepared : ∀ cell ∈ cells, ∃ value,
      cell.read (retiredState before row.start.word.toBitVec) =
        .ok value (retiredState before row.start.word.toBitVec) := by
    intro cell included
    obtain ⟨value, read⟩ := readable cell included
    exact ⟨value, cell_read_PC cell (cell_read_nextPC cell read _) _⟩
  have localReads : ∀ port ∈ worker.ports splitWorkers.cached,
      (readToken worker.assignment port).word.Bounded := by
    intro port physical
    apply reads (readToken worker.assignment port, worker.writeToken splitWorkers.cached port)
      (List.mem_append.mpr (Or.inr ?_))
    exact List.mem_flatMap.mpr ⟨worker, present, List.mem_map.mpr ⟨port, by simpa using physical, rfl⟩⟩
  obtain ⟨entry, included, source, pc, query, sameKind⟩ := unrolled_full_split_caller_source
    setup lookup accepted excluded initialPC row member family selected splitWorkers.cached worker matched
  have code := text_caller_code Keccak.Split.Caller.decoderFields text setup.size entry included
  have atCall := entry_source_after_history past
    (fun event present => readonly event (List.mem_filter.mp present).1) source code.1 code.2
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
  have clocks := state_clock_inputs (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned row member
  have advance := ClockLaws.advance (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus) trace.rom row
    (accepted.cpuEquations row member) clocks.1
  change (timeOfPair row.finish.timestamp).value = row.clock + 4 at advance
  refine ⟨before, after, past, ?_, ?_, entry, included, atCall, pc, query, sameKind, ?_⟩
  · change SailHistory cells (events.filter fun event => decide
      (row.clock < event.1 ∧ event.1 ≤ (timeOfPair row.finish.timestamp).value)) before after
    rw [advance]
    exact current
  · rw [advance]
    exact future
  · intro index arguments
    refine ⟨Keccak.Split.Native.Proofs.native_call_executes_of_history splitWorkers.cached worker
      (fixedEquations.rowsHold worker present) (active worker present) index arguments localReads
      localHistory localEvents aligned readable, retiredState after row.start.word.toBitVec, ?_, retirement⟩
    exact Keccak.Split.Native.Proofs.native_call_executes_of_history splitWorkers.cached worker
      (fixedEquations.rowsHold worker present) (active worker present) index
      (split_prepared_arguments arguments row.start.word.toBitVec) localReads
      (retired_state_history localHistory row.start.word.toBitVec) localEvents aligned prepared

end Airbender.Compiler.MachineTargets.Proofs
