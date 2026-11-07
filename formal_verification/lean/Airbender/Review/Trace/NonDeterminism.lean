import Airbender.Review.Trace.Execution
import Airbender.Review.Helpers.Decoder.ExternalInput

namespace Airbender.Trace.NonDeterminism
variable {p : Nat} [Fact p.Prime]

/-- State is Sail's state plus the external-stream position. Fetch and decode
    use the actual public bytes; the selected clause determines custom behavior. -/
def StepWithClause {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (clauseFor : List (BitVec 32) → Nat → SailRV32.instruction →
      Option (SailRV32.SailM SailRV32.ExecutionResult × Nat))
    (stream : List (BitVec 32)) (program : List (ProgramEntry Kind))
    (before after : Reference.RiscV.Sail.State × Nat) : Prop :=
  ∃ entry ∈ program, entry.SourceWith before.1 projection ∧
    Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) before.1 = .ok entry.pc before.1 ∧
    ∃ original, clauseFor stream before.2 entry.instruction = some (original, after.2) ∧
      Reference.Sail.run (Reference.RiscV.Sail.normalStep original) before.1 =
        .ok SailRV32.Functions.RETIRE_SUCCESS after.1

variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Existing external-input semantics with the selected standard ISA profile. -/
abbrev StepWith {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind)) (profile : ISAProfile) :=
  StepWithClause projection (fun stream position instruction => clause stream position instruction profile)

/-- Restricted-family execution uses the same relation and its named
    Airbender profile. Pooled execution selects unchanged standard Sail. -/
abbrev Step := StepWith decoderFields .airbender

/-- A finite mixed execution, carrying Sail state and the consumed-stream
    position at each step. The stream is fixed for the entire claim. -/
abbrev ExecutionTrace (stream : List (BitVec 32)) (program : List ProgramEntry) :=
  Relation.ReflTransGen (Step stream program)

end Airbender.Trace.NonDeterminism
