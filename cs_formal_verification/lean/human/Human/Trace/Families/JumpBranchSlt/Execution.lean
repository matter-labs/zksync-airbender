import Human.Helpers.Context.Registries.JumpBranchSltInputs
import Human.Trace.Execution

namespace Airbender.JumpBranchSlt
open Trace Reference.RiscV.Sail
open _root_.Sail.ArchSem

/-- Fetch, original Sail decoding, and the original generated execution clauses.
    This reuses the same step relation as the restricted arithmetic/memory trace. -/
abbrev SailStep := StepWith decoderFields Trace.instructionClause
abbrev SailTrace (program : List ProgramEntry) := Relation.ReflTransGen (SailStep program)

end Airbender.JumpBranchSlt
