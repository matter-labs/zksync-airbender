import Airbender.Proofs.Trace.ActiveDecoder
import Airbender.Review.Trace.Families.AddSub.SparseExecution

namespace Airbender.Trace

/-- The complete active setup decoder domain supplies initialized arithmetic
    execution. All native padding is retained; the final normalization row is excluded. -/
theorem active_setup_sail_execution {trace : Data mersenne31Modulus}
    {initial : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace initial cells)
    (image : AddSub.sparseDecoderSetupImage initial 7 20 = some AddSub.NativeSetup.setup)
    (accepted : Accepted trace)
    (decoded : ∀ row ∈ trace.rows,
      Verification.NativeSetup.DecoderContains .arithmetic row.decoderQuery)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Realizes (SailStep AddSub.NativeSetup.setup.program) trace initial cells :=
  sparse_public_sail_execution inputs image accepted (Proofs.active_arithmetic_decoded decoded) aligned

end Airbender.Trace
