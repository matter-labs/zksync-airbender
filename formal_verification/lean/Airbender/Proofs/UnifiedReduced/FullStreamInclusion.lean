import Airbender.Proofs.UnifiedReduced.StreamCalls

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Airbender.Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- The existing mixed ordinary/custom relation is a case of the merged
unified modular registry. -/
theorem mixed_step_to_modular {program : List (Trace.ProgramEntry UnifiedFamily)}
    {before after : State} (step : UnifiedReduced.Mixed.Step program before after) :
    UnifiedReduced.Modular.Step program before after := by
  rcases step with ⟨entry, member, source, pc, clause, selected, execution⟩
  refine ⟨entry, member, ?_, pc, clause, ?_, execution⟩
  · exact ⟨source.bytes, source.decoded, by
      simp [UnifiedReduced.Modular.decoderFields, source.fields]⟩
  · simp [UnifiedReduced.Modular.clauseFor, selected]

/-- Each old complete-call step embeds in the stream-aware unified machine
without consuming an external input word. -/
theorem full_step_to_stream {program : List (Trace.ProgramEntry UnifiedFamily)}
    {callers : List Delegation.Caller.ProgramEntry} {before after : State}
    (stream : List (BitVec 32)) (position : Nat)
    (step : Caller.FullStep program callers before after) :
    Caller.Stream.Step stream program callers (before, position) (after, position) := by
  rcases step with mixed | call
  · exact modular_step stream position callers (mixed_step_to_modular mixed)
  · obtain ⟨entry, member, source, pc, retirement⟩ := call
    exact caller_step stream position member source pc retirement

/-- The inclusion preserves arbitrary finite call/ordinary runs and their
stream position. -/
theorem full_run_to_stream {program : List (Trace.ProgramEntry UnifiedFamily)}
    {callers : List Delegation.Caller.ProgramEntry} {before after : State}
    (stream : List (BitVec 32)) (position : Nat)
    (run : Relation.ReflTransGen (Caller.FullStep program callers) before after) :
    Relation.ReflTransGen (Caller.Stream.Step stream program callers)
      (before, position) (after, position) := by
  induction run with
  | refl => exact .refl
  | tail previous step ih =>
    exact ih.tail (full_step_to_stream stream position step)

/-- Existing no-read whole-execution results become the empty-stream case of
the merged relation, with the same terminal PC and tracked cells. -/
theorem full_realizes_to_empty_stream {p : Nat} [Fact p.Prime]
    (program : List (Trace.ProgramEntry UnifiedFamily))
    (callers : List Delegation.Caller.ProgramEntry)
    (trace : UnifiedTrace p) (initial : State) (cells : List Cell)
    (view : MemoryToken p → MemoryToken p)
    (zeroReads : Caller.Stream.readCount trace = 0)
    (realizes : Trace.Realizes (Caller.FullStep program callers)
      trace initial cells view) :
    Caller.Stream.Realizes [] program callers trace initial cells view := by
  obtain ⟨after, run, pc, terminal⟩ := realizes
  refine ⟨after, ?_, pc, terminal⟩
  rw [zeroReads]
  exact full_run_to_stream [] 0 run

end Airbender.UnifiedReduced.Caller.Stream.Proofs
