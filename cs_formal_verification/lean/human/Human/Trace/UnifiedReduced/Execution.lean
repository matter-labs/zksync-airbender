import Human.Trace.Execution
import Human.Helpers.UnifiedReduced.ExecutionInputs

namespace Airbender.UnifiedReduced
open Trace Reference.RiscV.Sail

/-- Actual fetch, original Sail decoding and retirement for one unified row. -/
abbrev Step :=
  StepWith decoderFields instructionClause

end Airbender.UnifiedReduced
