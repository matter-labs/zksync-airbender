import Airbender.Review.Trace.Execution
import Airbender.Review.Helpers.UnifiedReduced.ExecutionInputs

namespace Airbender.UnifiedReduced
open Trace Reference.RiscV.Sail

/-- Actual fetch, original Sail decoding and retirement for one unified row. -/
abbrev Step [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] :=
  StepWith decoderFields instructionClause

end Airbender.UnifiedReduced
