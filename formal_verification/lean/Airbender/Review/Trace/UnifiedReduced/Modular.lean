import Airbender.Review.Helpers.UnifiedReduced.Modular
import Airbender.Review.Trace.Execution

namespace Airbender.UnifiedReduced.Modular

/-- Public fetch, selected standard/project clause and ordinary retirement. -/
abbrev Step [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] :=
  Trace.StepWith decoderFields clauseFor

end Airbender.UnifiedReduced.Modular
