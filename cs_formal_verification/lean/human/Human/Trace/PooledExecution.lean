import Human.Helpers.Context.PooledBoundary
import Human.Trace.Execution

namespace Airbender.Trace
open Reference.RiscV.Sail

/-- One step of an admitted six-family program, using actual Sail fetch,
    decoding and original instruction execution. No custom ISA profile is selected. -/
abbrev PooledStep := StepWith pooledDecoderFields instructionClause

end Airbender.Trace
