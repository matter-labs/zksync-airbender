import Airbender.Review.UnifiedReduced.Execution
import Airbender.Review.UnifiedReduced.CustomExecution

namespace Airbender.UnifiedReduced.Mixed
open Trace Reference.RiscV.Sail

/-- One metadata registry for standard unified instructions and the admitted
    TRIADD/XORROT MOPs. Both branches reuse their existing native projections;
    original Sail decoding supplies the instruction, not the circuit witness. -/
def decoderFields (instruction : SailRV32.instruction) : Option (DecoderData UnifiedFamily) :=
  UnifiedReduced.decoderFields instruction <|> customDecoderFields instruction

/-- Read actual public bytes and run the pinned Sail decoder once for the
    combined program. Unsupported encodings and missing bytes remain failures. -/
abbrev programImage := programImageRunWith decoderFields

/-- Standard rows call original Sail execution. Project MOPs call the same
    pinned custom clauses used by TRIADD/XORROT soundness. Unsupported operations
    have no clause; upstream Zimop fallback is not substituted. -/
def clauseFor [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (instruction : SailRV32.instruction) : Option (SailRV32.SailM SailRV32.ExecutionResult) :=
  instructionClause instruction <|> Custom.clauseFor instruction

/-- Shared fetch/decoding/retirement relation for the combined registry.
    Mixed memory transport is checked; whole mixed instruction retirement is
    the subsequent connection to the existing per-instruction proofs. -/
abbrev Step [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] :=
  StepWith decoderFields clauseFor

end Airbender.UnifiedReduced.Mixed
