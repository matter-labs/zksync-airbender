import Airbender.Proofs.Reduced.CallerCycles
import Airbender.Proofs.Trace.IndexedCycleComposition
import Airbender.Proofs.Trace.ExternalComposition

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail Delegation.Caller Delegation.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000

/-- Native ordinary and complete caller cycles share one reduced indexed transition. -/
theorem full_cycle_transition [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List PooledProgramEntry}
    {initial finalState : State} {ca oa : List (BitVec 32)} {cells : List Cell} {events : List MemoryAccess}
    (accepted : MixedMemoryAccepted data program) (inputs : StreamMemoryInputs data program initial ca oa cells)
    (code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (callerAllowed : ∀ entry ∈ data.program, Caller.reducedCall entry.data.family)
    (families : ∀ row ∈ data.machine.rows, Caller.reducedFamily row.family = true)
    (unchanged : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    (requests : RequestBinding data initial)
    (order : events.Pairwise (fun a b => b.1 ≤ a.1)) (stream : List (BitVec 32))
    (ordinary : ∀ row ∈ data.machine.rows, row ∉ data.callers →
      Caller.OrdinaryCycle stream program data.machine cells events initial finalState row)
    (callers : ∀ row ∈ data.callers, FullCallerCycle data initial finalState cells events row)
    {row : Trace.Row babyBearModulus PooledFamily} (member : row ∈ data.machine.rows) :
    ∃ before after,
      CutState cells events initial (Delegation.Caller.startClock row) before ∧
      CutState cells events initial (Delegation.Caller.finishClock row) after ∧
      Caller.ReducedStep stream program data.program
        (retiredState before row.start.word.toBitVec, Caller.countAt data.machine row.clock)
        (retiredState after row.finish.word.toBitVec,
          Caller.countAt data.machine (Delegation.Caller.finishClock row)) ∧
      (run (SailRV32.Functions.get_arch_pc ()) before = .ok row.start.word.toBitVec before →
        Caller.ReducedStep stream program data.program (before, Caller.countAt data.machine row.clock)
          (retiredState after row.finish.word.toBitVec,
            Caller.countAt data.machine (Delegation.Caller.finishClock row))) := by
  have clocks := machine_clock_facts (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram member
  by_cases caller : row ∈ data.callers
  · obtain ⟨before, after, past, current, _, entry, included, query, pc, source, raw, retired⟩ := callers row caller
    have noRead : External.isRead row = false := by
      have family := (caller_member caller).2
      have holds := accepted.constraints row member
      cases row with
      | mk kind w =>
        cases family
        have core := Verification.holds_of_sublist holds
          (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
        exact native_caller_read_disabled (by decide) core query
    have sameCount : Caller.countAt data.machine (Delegation.Caller.finishClock row) =
        Caller.countAt data.machine row.clock := by
      simpa [Caller.countAt, noRead] using native_cycle_count accepted.toRequestChecks inputs.publicProgram member
    refine ⟨before, after, past, history_prefix_of_window order (by omega) past current,
      Or.inr ⟨sameCount.symm, entry, included, callerAllowed entry included,
        entry_source_retired_state source _, ?_, retired⟩, ?_⟩
    · rw [← pc]; exact retired_state_pc before _
    · intro read
      refine Or.inr ⟨sameCount.symm, entry, included, callerAllowed entry included,
        source, pc ▸ read, after, raw, ?_⟩
      exact caller_pc_retirement_raw requests caller (sail_history_pc_read current read)
  · obtain ⟨entry, included, family, query, clause, next, selected, counter,
        before, after, past, current, _, retired⟩ := ordinary row member caller
    have pcWord := native_query_pc_word (by decide) query
    change row.start.word = Word.ofBitVec entry.pc at pcWord
    have pc := (congrArg Word.toBitVec pcWord).trans (Word.ofBitVec_roundtrip _)
    have source := entry_source_after_history past
      (fun event present => unchanged event (List.mem_filter.mp present).1)
      (run_program_sources inputs.ordinaryProgram entry included)
      (code entry included).1 (code entry included).2
    have reduced : entry.SourceWith (retiredState before row.start.word.toBitVec)
        Caller.reducedDecoderFields := by
      have current := entry_source_retired_state source row.start.word.toBitVec
      refine ⟨current.bytes, current.decoded, ?_⟩
      have allowed : Caller.reducedFamily entry.data.family = true := family ▸ families row member
      simp [Caller.reducedDecoderFields, current.fields, allowed]
    have nextCount : next = Caller.countAt data.machine (Delegation.Caller.finishClock row) :=
      counter.trans (native_cycle_count accepted.toRequestChecks inputs.publicProgram member).symm
    have step : NonDeterminism.StepWithClause Caller.reducedDecoderFields External.clause
        stream program
        (retiredState before row.start.word.toBitVec, Caller.countAt data.machine row.clock)
        (retiredState after row.finish.word.toBitVec,
          Caller.countAt data.machine (Delegation.Caller.finishClock row)) := by
      refine ⟨entry, included, reduced, pc ▸ retired_state_pc before _, clause, ?_, retired⟩
      rw [← nextCount]
      exact selected
    exact ⟨before, after, past,
      history_prefix_of_window order (by
        change (timeOfPair row.start.timestamp).value ≤ (timeOfPair row.finish.timestamp).value
        have advance := clocks.2
        change (timeOfPair row.finish.timestamp).value = (timeOfPair row.start.timestamp).value + 4 at advance
        omega) past current,
      Or.inl step, fun read => Or.inl (ExternalStream.Proofs.step_of_rebased_with_clause read step)⟩

end Airbender.AddSub.Modular.External.Caller.Proofs
