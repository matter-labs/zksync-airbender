import Human.Trace.Execution
import Human.Helpers.UnifiedReduced.Program

namespace Airbender.UnifiedReduced.Mixed
open Trace Reference.RiscV.Sail

/-- Shared fetch/decoding/retirement relation for the combined registry.
    `Mixed.execution_soundness` connects each native row and the final public
    observations to this relation, including native ROM-shadow transport. -/
abbrev Step [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] :=
  StepWith decoderFields clauseFor

end Airbender.UnifiedReduced.Mixed
