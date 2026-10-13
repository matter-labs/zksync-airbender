import Airbender.Review.Helpers.UnifiedReduced.CustomInputs
import Airbender.Review.Trace.Execution

namespace Airbender.UnifiedReduced.Custom
open Trace Reference.RiscV.Sail

/-- Actual public fetch, original Sail decoding and retirement of one supported
    project instruction. The reference clause depends only on the fetched AST. -/
abbrev Step := StepWith customDecoderFields clauseFor

end Airbender.UnifiedReduced.Custom
