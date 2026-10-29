import Airbender.Review.Trace.Modular.ExternalCalls

namespace Airbender.AddSub.Modular.External.Caller
open Airbender.Trace Reference.RiscV.Sail
set_option warningAsError true

/-- The native four-family filter preserves a sourced ordinary instruction. -/
theorem source_reduced (entry : PooledProgramEntry) (before : State)
    (family : reducedFamily entry.data.family = true)
    (source : entry.SourceWith before AddSub.Modular.External.decoderFields) :
    entry.SourceWith before reducedDecoderFields := by
  refine ⟨source.bytes, source.decoded, ?_⟩
  simp [reducedDecoderFields, source.fields, family]

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Every ordinary step whose public program uses only the four native reduced
families is also a step of the reduced machine. -/
theorem ordinary_step_reduced (stream : List (BitVec 32))
    (program : List PooledProgramEntry)
    (callers : List Delegation.Caller.ProgramEntry)
    (family : ∀ entry ∈ program, reducedFamily entry.data.family = true)
    {before after : State × Nat}
    (step : AddSub.Modular.External.Step stream program before after) :
    ReducedStep stream program callers before after := by
  left
  obtain ⟨entry, member, source, pc, original, clause, retire⟩ := step
  exact ⟨entry, member, source_reduced entry before.1 (family entry member) source,
    pc, original, clause, retire⟩

/-- The call branch is unchanged; its allowed family is still BLAKE2 round. -/
theorem step_reduced (stream : List (BitVec 32))
    (program : List PooledProgramEntry)
    (callers : List Delegation.Caller.ProgramEntry)
    (family : ∀ entry ∈ program, reducedFamily entry.data.family = true)
    {before after : State × Nat}
    (step : Step reducedCall stream program callers before after) :
    ReducedStep stream program callers before after := by
  rcases step with ordinary | call
  · exact ordinary_step_reduced stream program callers family ordinary
  · exact Or.inr call

/-- Lift a finite stream-aware run through the reduced-family restriction. -/
theorem execution_reduced (stream : List (BitVec 32))
    (program : List PooledProgramEntry)
    (callers : List Delegation.Caller.ProgramEntry)
    (family : ∀ entry ∈ program, reducedFamily entry.data.family = true)
    {before after : State × Nat}
    (run : Relation.ReflTransGen (Step reducedCall stream program callers) before after) :
    Relation.ReflTransGen (ReducedStep stream program callers) before after :=
  Relation.ReflTransGen.mono
    (fun _ _ h => step_reduced stream program callers family h) run

/-- The reduced-machine terminal relation retains exact stream consumption,
native terminal PC and every tracked terminal cell. -/
theorem realizes_reduced {p : Nat} [Fact p.Prime]
    (stream : List (BitVec 32)) (program : List PooledProgramEntry)
    (callers : List Delegation.Caller.ProgramEntry)
    (trace : PooledTrace p) (initial : State) (cells : List Cell)
    (view : MemoryToken p → MemoryToken p)
    (family : ∀ entry ∈ program, reducedFamily entry.data.family = true)
    (realizes : Realizes reducedCall stream program callers trace initial cells view) :
    ReducedRealizes stream program callers trace initial cells view := by
  obtain ⟨after, run, pc, terminal⟩ := realizes
  exact ⟨after, execution_reduced stream program callers family run, pc, terminal⟩

end Airbender.AddSub.Modular.External.Caller
