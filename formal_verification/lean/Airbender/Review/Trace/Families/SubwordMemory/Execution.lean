import Airbender.Review.Helpers.Registries.SubwordMemoryInputs
import Airbender.Review.Trace.Execution

namespace Airbender.SubwordMemory
open Trace Reference.RiscV.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

abbrev SailStep := StepWith decoderFields Trace.instructionClause
abbrev SailTrace (program : List ProgramEntry) := Relation.ReflTransGen (SailStep program)

end Airbender.SubwordMemory
