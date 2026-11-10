import Airbender.Review.Trace.UnifiedReduced.StreamCalls
import Airbender.Proofs.UnifiedReduced.StreamCycleDispatch
import Airbender.Proofs.UnifiedReduced.StreamClockCount
import Airbender.Proofs.UnifiedReduced.FullComposition
import Airbender.Proofs.Trace.ExternalComposition
import Airbender.Proofs.Trace.IndexedCycleComposition

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
open Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000

/-- Native caller and noncaller cycles give one common indexed transition. -/
theorem full_cycle_transition [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial finalState : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {events : List MemoryAccess}
    (accepted : MixedMemoryAccepted data program)
    (inputs : NativeMemoryInputsWith Stream.decoderFields data program initial ca oa cells)
    (code : CodeProfile data program cells) (requests : RequestBinding data initial)
    (order : events.Pairwise (fun a b => b.1 ≤ a.1)) (stream : List (BitVec 32))
    (ordinary : ∀ row ∈ data.machine.rows, row ∉ data.callers →
      Stream.OrdinaryCycle stream program data.machine cells events initial finalState row)
    (callers : ∀ row ∈ data.callers,
      FullCallerCycle data initial finalState cells events row)
    {row : Trace.Row babyBearModulus UnifiedFamily} (member : row ∈ data.machine.rows) :
    ∃ before after,
      CutState cells events initial (Delegation.Caller.startClock row) before ∧
      CutState cells events initial (Delegation.Caller.finishClock row) after ∧
      Stream.Step stream program data.program
        (retiredState before row.start.word.toBitVec, Stream.countAt data.machine row.clock)
        (retiredState after row.finish.word.toBitVec,
          Stream.countAt data.machine (Delegation.Caller.finishClock row)) ∧
      (run (SailRV32.Functions.get_arch_pc ()) before = .ok row.start.word.toBitVec before →
        Stream.Step stream program data.program (before, Stream.countAt data.machine row.clock)
          (retiredState after row.finish.word.toBitVec,
            Stream.countAt data.machine (Delegation.Caller.finishClock row))) := by
  have clocks := machine_clock_facts (by decide) (by decide)
    accepted.toRequestChecks inputs.publicProgram member
  by_cases caller : row ∈ data.callers
  · have noRead : Stream.isRead row = false := by
      cases row with
      | mk family assignment =>
        cases family
        have core := Verification.holds_of_sublist (accepted.constraints _ member)
          (List.sublist_append_left (importedConstraints data.machine.rom)
            importedConstraintsTimestampLookups)
        exact native_caller_read_disabled (by decide) core (accepted.active _ member)
          (of_decide_eq_true (List.mem_filter.mp caller).2)
    have sameCount : Stream.countAt data.machine (Delegation.Caller.finishClock row) =
        Stream.countAt data.machine row.clock := by
      simpa [Stream.countAt, noRead] using
        native_cycle_count accepted.toRequestChecks inputs.publicProgram member
    obtain ⟨before, after, past, current, _, entry, included, _, pc, source, raw, retired⟩ :=
      callers row caller
    refine ⟨before, after, past, history_prefix_of_window order (by omega) past current,
      Or.inr ⟨sameCount.symm, entry, included, entry_source_retired_state source _, ?_, retired⟩, ?_⟩
    · rw [← pc]
      exact retired_state_pc before _
    · intro read
      refine Or.inr ⟨sameCount.symm, entry, included, source, pc ▸ read, after, raw, ?_⟩
      exact caller_pc_retirement_raw requests caller (sail_history_pc_read current read)
  · obtain ⟨entry, included, query, clause, next, selected, counter,
        before, after, past, current, _, retired⟩ := ordinary row member caller
    have pcWord : row.start.word = Word.ofBitVec entry.pc := by
      cases row with
      | mk family assignment =>
        cases family
        exact native_query_pc_word (by decide) query
    have pc := (congrArg Word.toBitVec pcWord).trans (Word.ofBitVec_roundtrip _)
    have source := cycle_source past (run_program_sources inputs.ordinaryProgram entry included)
      code.ram (code.ordinary entry included) pc
    have nextCount : next = Stream.countAt data.machine (Delegation.Caller.finishClock row) :=
      counter.trans (native_cycle_count accepted.toRequestChecks inputs.publicProgram member).symm
    have step : NonDeterminism.StepWithClause Stream.decoderFields Stream.clauseFor
        stream program
        (retiredState before row.start.word.toBitVec, Stream.countAt data.machine row.clock)
        (retiredState after row.finish.word.toBitVec,
          Stream.countAt data.machine (Delegation.Caller.finishClock row)) := by
      refine ⟨entry, included, source, pc ▸ retired_state_pc before _, clause, ?_, retired⟩
      rw [← nextCount]
      exact selected
    exact ⟨before, after, past,
      history_prefix_of_window order (by
        change (timeOfPair row.start.timestamp).value ≤ (timeOfPair row.finish.timestamp).value
        have advance := clocks.2
        change (timeOfPair row.finish.timestamp).value =
          (timeOfPair row.start.timestamp).value + 4 at advance
        omega) past current,
      Or.inl step, fun read => Or.inl
        (ExternalStream.Proofs.step_of_rebased_with_clause read step)⟩

end Airbender.UnifiedReduced.Caller.Stream.Proofs
