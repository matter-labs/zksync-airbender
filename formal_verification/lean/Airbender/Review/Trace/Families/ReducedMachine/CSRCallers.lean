import Airbender.Proofs.Trace.Families.ReducedMachine.CSRCallers

namespace Airbender.ReducedMachine.Native
open Trace Reference.RiscV.Sail
set_option autoImplicit false

/-- Full original public CSR sources and accepted initialized native matching
    derive source/request history and chronological native caller observations.
    Caller clocks are bounded/nonzero/unique and use the exact imported offset.
    Actual issuance, worker fulfillment/converse and protocol enforcement remain separate. -/
theorem public_runtime_csr_callers {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup CSRMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : csrDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (runtimeCSRData trace) initial cells)
    (accepted : Accepted (runtimeCSRData trace)) (decoded : CSRDecodedTrace trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    CSRRequestHistory (runtimeCSRData trace) setup initial cells ∧
      ∃ callers, CSRCallerProjection (runtimeCSRData trace) callers :=
  NativeCSRCallerProofs.image_callers image inputs accepted decoded aligned

end Airbender.ReducedMachine.Native
