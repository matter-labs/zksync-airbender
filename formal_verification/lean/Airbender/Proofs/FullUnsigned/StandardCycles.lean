import Airbender.Proofs.FullUnsigned.StandardCalls
import Airbender.Proofs.FullUnsigned.StandardPC
import Airbender.Proofs.FullUnsigned.CallHistory
import Airbender.Proofs.Trace.CycleComposition

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Standard full callers execute their complete native memory call and original
Sail PC retirement at the exact common-history cuts. Input contracts stay explicit. -/
theorem unrolled_full_standard_caller_cycle
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
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (facts : Transfer.Facts (unrolledFullMemoryData trace workers splitWorkers))
    {cells : List Cell}
    (inputs : Transfer.NativeInputs (unrolledFullMemoryData trace workers splitWorkers) initial cells)
    (workerSetup : workers.setup = Delegation.modeledSetup Keccak.Controller.rows)
    (bounds : ∀ edge ∈ (unrolledFullMemoryData trace workers splitWorkers).steps,
      edge.1.word.Bounded ∧ edge.2.word.Bounded)
    (ram : ExternalBoundary.WorkerRAM.Binding workers.rows)
    (commands : ∀ worker ∈ workers.rows, worker.family = .bigint →
      ∃ command, ExternalBoundary.BigintABI.Binding worker.assignment command)
    (controls : ∀ w, (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ workers.rows →
      ExternalBoundary.HashABI.RoundControl w)
    (row : Trace.Row babyBearModulus PooledFamily) (member : row ∈ trace.rows)
    (family : row.family = .addSub) (selected : Delegation.Requests.Selected row.assignment)
    (worker : Delegation.Row babyBearModulus) (present : worker ∈ workers.rows)
    (workerFamily : FullUnsigned.standardCall worker.family)
    (matched : Delegation.Requests.fulfillment worker = Delegation.Requests.caller row.assignment)
    {events : List MemoryAccess}
    (permutation : events.Perm ((unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (readonly : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.Caller.FullCallerCycle
      ⟨trace, workers, FullUnsigned.entriesWith FullUnsigned.standardDecoderFields text⟩
      initial finalState cells events row := by
  obtain ⟨before, after, past, localHistory, localEvents, future⟩ :=
    unrolled_full_standard_caller_history setup lookup accepted excluded initialPC equations active
      initialClock initialAligned row member family selected worker present matched permutation ordered history
  let low := row.clock
  obtain ⟨cutBefore, cutAfter, _, cutPast, current, _⟩ :=
    history_window ordered history (by omega : low ≤ low + 4)
  have sameBefore := sail_history_deterministic past cutPast
  subst cutBefore
  have sameAfter := sail_history_deterministic localHistory (history_without_zero current)
  subst cutAfter
  have initialized : ∀ cell ∈ cells, ∃ value, cell.read initial = .ok value initial := by
    intro cell included
    obtain ⟨_, _, _, read, _⟩ := Transfer.native_cell_source inputs included
    exact ⟨_, read⟩
  have readable := history_cells_readable past aligned initialized
  have raw := unrolled_full_standard_worker_call accepted equations active initialClock initialAligned
    facts inputs.toBoundaryInputs workerSetup bounds ram commands controls present workerFamily
    localHistory localEvents aligned readable
  have prepared : ∀ cell ∈ cells, ∃ value,
      cell.read (retiredState before row.start.word.toBitVec) =
        .ok value (retiredState before row.start.word.toBitVec) := by
    intro cell included
    obtain ⟨value, read⟩ := readable cell included
    exact ⟨value, cell_read_PC cell (cell_read_nextPC cell read _) _⟩
  have rebased := unrolled_full_standard_worker_call accepted equations active initialClock initialAligned
    facts inputs.toBoundaryInputs workerSetup bounds ram commands controls present workerFamily
    (retired_state_history localHistory row.start.word.toBitVec) localEvents aligned prepared
  obtain ⟨entry, included, source, pc, query, sameFamily⟩ := unrolled_full_standard_caller_source
    setup lookup accepted excluded initialPC row member family selected worker matched
  have code := text_caller_code FullUnsigned.standardDecoderFields text setup.size entry included
  have atCall := entry_source_after_history past
    (fun event present => readonly event (List.mem_filter.mp present).1) source code.1 code.2
  have pcBinding := unrolled_full_standard_pc_binding setup lookup accepted excluded initialPC
    row member family selected worker matched
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
  refine ⟨before, after, past, ?_, ?_, entry, included, query, pc, atCall,
    sameFamily ▸ raw, retiredState after row.start.word.toBitVec, sameFamily ▸ rebased, retirement⟩
  · change SailHistory cells (events.filter fun event => decide
      (row.clock < event.1 ∧ event.1 ≤ (timeOfPair row.finish.timestamp).value)) before after
    rw [advance]
    exact current
  · change SailHistory cells (events.filter fun event => decide
      ((timeOfPair row.finish.timestamp).value < event.1)) after finalState
    rw [advance]
    exact future

end Airbender.Compiler.MachineTargets.Proofs
