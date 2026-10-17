import Airbender.Proofs.Trace.Composition
import Airbender.Review.Trace.Families.AddSub.Execution
import Airbender.Proofs.Mersenne31

namespace Airbender.Trace

/-- Public initial state/program construction and accepted native constraints
    derive complete selected arithmetic execution and exact terminal PC/cells.
    Only public RAM-cell alignment is supplied. Actual code-byte reads, original Sail decoding
    and normal retirement are checked; physical setup fidelity, cryptographic
    enforcement, other ISA families and completeness remain separate. -/
theorem public_sail_execution {trace : Data mersenne31Modulus} {setup : DecoderSetup}
    {initial : Reference.RiscV.Sail.State} {cells : List Cell} {count logCapacity : Nat}
    (inputs : ImageBoundary trace initial cells)
    (image : decoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Realizes (SailStep setup.program) trace initial cells :=
  Proofs.image_execution_soundness (by decide) inputs image accepted decoded aligned

end Airbender.Trace
