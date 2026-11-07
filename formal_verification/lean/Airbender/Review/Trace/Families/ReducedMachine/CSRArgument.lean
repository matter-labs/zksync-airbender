import Airbender.Proofs.Trace.Families.ReducedMachine.CSRArgument

namespace Airbender.ReducedMachine.Native
open Trace Reference.RiscV.Sail
set_option autoImplicit false

/-- Accepted initialized native CSR callers connect to the reviewed native
    stage2 and quotient argument formulas, preserving original source history.
    Arbitrary challenges/embedding remain explicit; no compression injectivity,
    LDE correspondence, actual issuance or worker ledger is inferred. -/
theorem public_runtime_csr_argument {R : Type} [CommRing R]
    (embed : ZMod mersenne31Modulus →+* R) (ch : CSRArgumentChallenges R)
    {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup CSRMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : csrDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (runtimeCSRData trace) initial cells)
    (accepted : Accepted (runtimeCSRData trace)) (decoded : CSRDecodedTrace trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    CSRRequestHistory (runtimeCSRData trace) setup initial cells ∧
      ∃ callers, CSRCallerProjection (runtimeCSRData trace) callers ∧
        CSRCallerArgumentProjection embed ch (runtimeCSRData trace) callers :=
  NativeCSRArgumentProofs.image_argument embed ch image inputs accepted decoded aligned

end Airbender.ReducedMachine.Native
