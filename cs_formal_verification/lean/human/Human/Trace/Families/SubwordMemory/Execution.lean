import Human.Helpers.Context.Registries.SubwordMemoryInputs
import Human.Trace.Execution

namespace Airbender.SubwordMemory
open Trace Reference.RiscV.Sail
open _root_.Sail.ArchSem

abbrev SailStep := StepWith decoderFields Trace.instructionClause
abbrev SailTrace (program : List ProgramEntry) := Relation.ReflTransGen (SailStep program)

end Airbender.SubwordMemory
