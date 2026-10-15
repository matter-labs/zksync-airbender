import Airbender.Proofs.UnifiedReduced.ModularComposition
import Airbender.Review.Helpers.Context.PaddingBoundary.Theorems

namespace Airbender.UnifiedReduced.Modular
open Trace
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Standard instructions, TRIADD/XORROT and all four modular operations execute
    together from native boot in BabyBear. Public bytes select original Sail
    ASTs; initialized matching derives operands, old destinations and word
    bounds. Final PC/cells agree with terminal tokens through the ROM view. -/
theorem execution_soundness
    {trace : UnifiedTrace babyBearModulus} {initial : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List ProgramEntry}
    (inputs : Inputs trace initial cells program)
    (accepted : Accepted trace) (decoded : Decoded trace program) :
    Realizes (Step program) trace initial cells (Trace.ROMView.token initial) :=
  Proofs.trace_execution (by decide) (by decide) (by decide) inputs accepted decoded

/-- The same execution after erasing inactive rows using external exact masked
    closure. Imported raw constraints and the public boot conditions remain. -/
theorem padded_execution_soundness
    {trace : UnifiedTrace babyBearModulus} {initial : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List ProgramEntry}
    (inputs : Inputs (PaddingBoundary.active trace) initial cells program)
    (accepted : PaddingBoundary.AcceptedLayout trace)
    (decoded : Decoded (PaddingBoundary.active trace) program) :
    Realizes (Step program) trace initial cells (Trace.ROMView.token initial) :=
  execution_soundness (trace := PaddingBoundary.active trace) inputs
    (PaddingBoundary.acceptance_soundness accepted) decoded

end Airbender.UnifiedReduced.Modular
