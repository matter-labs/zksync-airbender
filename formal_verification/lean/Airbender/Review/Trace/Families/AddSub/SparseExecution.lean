import Airbender.Proofs.Trace.SparseExecution
import Airbender.Review.Trace.Families.AddSub.Execution
import Airbender.Proofs.Mersenne31

namespace Airbender.Trace

/-- Actual sparse public construction and complete native matching derive
    original fetched arithmetic execution and exact terminal PC/cells.
    Unsupported words retain their slots; accepted rows cannot select them. -/
theorem sparse_public_sail_execution {trace : Data mersenne31Modulus}
    {setup : SparseDecoderSetup Family} {initial : Reference.RiscV.Sail.State}
    {cells : List Cell} {count logCapacity : Nat}
    (inputs : ImageBoundary trace initial cells)
    (image : AddSub.sparseDecoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : AddSub.SparseDecoded trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Realizes (SailStep setup.program) trace initial cells :=
  Proofs.sparse_image_execution_soundness (by decide) inputs image accepted decoded aligned

end Airbender.Trace
