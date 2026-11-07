import Airbender.Proofs.Trace.Families.ReducedMachine.CSRRegisterHistory

import Airbender.Review.Trace.Families.ReducedMachine.RuntimeCSRData

namespace Airbender.ReducedMachine.Native
open Trace Reference.RiscV.Sail
set_option autoImplicit false

/-- Public bytes/decoding, seed reads and accepted actual native matching derive
    every original Sail GPR observation/write and instruction segment state,
    preserved code/misa and final cell matching. No per-row read, state or result
    is supplied. Original CSR instruction/privilege effects, PC and physical setup remain separate. -/
theorem public_csr_register_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup CSRMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : csrDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace)
    (decoded : CSRDecodedTrace trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    CSRRegisterHistory trace setup initial cells :=
  NativeCSRRegisterProofs.image_register_history image inputs accepted decoded aligned

/-- Original GPR reads/write and all segment states under the explicit runtime
    pool. Original CSR clause execution and caller issuance remain separate. -/
theorem public_runtime_csr_register_history {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup CSRMode} {initial : State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : csrDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary (runtimeCSRData trace) initial cells) (accepted : Accepted (runtimeCSRData trace))
    (decoded : CSRDecodedTrace trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    CSRRegisterHistory (runtimeCSRData trace) setup initial cells :=
  NativeCSRRegisterProofs.image_register_history (trace := runtimeCSRData trace) image inputs accepted decoded aligned

end Airbender.ReducedMachine.Native
