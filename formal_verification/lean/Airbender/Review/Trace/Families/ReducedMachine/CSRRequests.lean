import Airbender.Proofs.Trace.Families.ReducedMachine.CSRRequests

namespace Airbender.ReducedMachine.Native
open Trace Reference.RiscV.Sail
set_option autoImplicit false

/-- Full public bytes, accepted runtime constraints and initialized matching
    derive original pre-state rs1 words and request ABI observations in the same
    chronological GPR history. No source/read/range/request/state is supplied.
    Actual issuance, original CSR retirement and worker effects remain separate. -/
theorem public_runtime_csr_requests {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup CSRMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : csrDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (runtimeCSRData trace) initial cells)
    (accepted : Accepted (runtimeCSRData trace)) (decoded : CSRDecodedTrace trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    CSRRequestHistory (runtimeCSRData trace) setup initial cells :=
  NativeCSRSourceProofs.image_request_history image inputs accepted decoded aligned

end Airbender.ReducedMachine.Native
