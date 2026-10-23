import Airbender.Review.Helpers.UnifiedReduced.ExecutionInputs
import Airbender.Review.Helpers.UnifiedReduced.CustomInputs

namespace Airbender.UnifiedReduced.Mixed
open Trace Reference.RiscV.Sail

/-- One metadata registry for standard unified instructions and the admitted
    TRIADD/XORROT MOPs. Both branches reuse their existing native projections;
    original Sail decoding supplies the instruction, not the circuit witness. -/
def decoderFields (instruction : SailRV32.instruction) : Option (DecoderData UnifiedFamily) :=
  UnifiedReduced.decoderFields instruction <|> customDecoderFields instruction

/-- The standard/custom registry uses the same public boot, readonly code,
    configuration and supported-load profile as standard execution. Reads,
    ranges and instruction results are derived from the shared history. -/
abbrev Inputs {p : Nat} [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] :=
  ExecutionInputsWith (p := p) decoderFields

/-- Read actual public bytes and run the pinned Sail decoder once for the
    combined program. Unsupported encodings and missing bytes remain failures. -/
abbrev programImage := programImageRunWith decoderFields

/-- Standard rows call original Sail execution. Project MOPs call the same
    pinned custom clauses used by TRIADD/XORROT soundness. Unsupported operations
    have no clause; upstream Zimop fallback is not substituted. -/
def clauseFor [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (instruction : SailRV32.instruction) : Option (SailRV32.SailM SailRV32.ExecutionResult) :=
  instructionClause instruction <|> Custom.clauseFor instruction

end Airbender.UnifiedReduced.Mixed
