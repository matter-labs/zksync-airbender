import Human.Trace.Execution
import Human.Helpers.Decoder.ExternalInput

namespace Airbender.Trace.NonDeterminism
variable {p : Nat} [Fact p.Prime]
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- State is Sail's state plus the external-stream position. Fetch and decode
    use the actual public bytes; custom behavior is visible in `clause` above. -/
def StepWith {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind)) (profile : ISAProfile)
    (stream : List (BitVec 32)) (program : List (ProgramEntry Kind))
    (before after : Reference.RiscV.Sail.State × Nat) : Prop :=
  ∃ entry ∈ program, entry.SourceWith before.1 projection ∧
    Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) before.1 = .ok entry.pc before.1 ∧
    ∃ original, clause stream before.2 entry.instruction profile = some (original, after.2) ∧
      Reference.Sail.run (Reference.RiscV.Sail.normalStep original) before.1 =
        .ok SailRV32.Functions.RETIRE_SUCCESS after.1

/-- Restricted-family execution uses the same relation and its named
    Airbender profile. Pooled execution selects unchanged standard Sail. -/
abbrev Step := StepWith decoderFields .airbender

/-- A finite mixed execution, carrying Sail state and the consumed-stream
    position at each step. The stream is fixed for the entire claim. -/
abbrev ExecutionTrace (stream : List (BitVec 32)) (program : List ProgramEntry) :=
  Relation.ReflTransGen (Step stream program)

end Airbender.Trace.NonDeterminism
