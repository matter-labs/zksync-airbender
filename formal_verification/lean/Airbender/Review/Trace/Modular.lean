import Airbender.Review.Helpers.Decoder.ModularProgram
import Airbender.Review.Helpers.Context.PooledBoundary
import Airbender.Review.Trace.Execution

namespace Airbender.AddSub.Modular.Pooled
open Trace
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Actual public fetch and retirement for the six ordinary circuit families
    plus ADDMOD/SUBMOD/MULMOD/FMAMOD, using the pinned project modular clauses. -/
abbrev Step := StepWith decoderFields clauseFor

end Airbender.AddSub.Modular.Pooled
