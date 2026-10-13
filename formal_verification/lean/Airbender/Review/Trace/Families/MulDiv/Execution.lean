import Airbender.Review.Helpers.Context.Registries.MulDivInputs
import Airbender.Review.Trace.Execution

namespace Airbender.MulDiv
open Trace Reference.RiscV.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

/-- Original Sail fetch/decoding, execution and retirement, using the same
    step relation as the arithmetic/memory and jump-family traces. -/
abbrev SailStep := StepWith decoderFields Trace.instructionClause
abbrev SailTrace (program : List ProgramEntry) := Relation.ReflTransGen (SailStep program)

end Airbender.MulDiv
