import Airbender.Review.Trace.Execution

namespace Airbender.Trace
open Reference.RiscV.Sail
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- The original ADD/SUB trace also admits word-memory rows. These aliases
    select that two-family decoder and retain the explicit ISA profile. -/
abbrev Step (profile : ISAProfile) := StepWith decoderFields (profileClause profile)

/-- A finite sequence of the checked Sail steps, including an empty trace. -/
abbrev ExecutionTrace (profile : ISAProfile) (program : List ProgramEntry) :=
  Relation.ReflTransGen (Step profile program)

abbrev SailStep := Step .sail
abbrev SailTrace := ExecutionTrace .sail
abbrev AirbenderTrace := ExecutionTrace .airbender

end Airbender.Trace
