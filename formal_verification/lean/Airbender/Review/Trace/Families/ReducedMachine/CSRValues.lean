import Airbender.Proofs.Trace.Families.ReducedMachine.CSRValues

import Airbender.Review.Trace.Families.ReducedMachine.RuntimeCSRData

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Public seed reads, actual native acceptance with explicit modeled setup and original public
    CSR decoding derive all native word ranges, including discarded reads/writes.
    No per-row value, clock, selector, range or expected read is supplied. -/
theorem public_csr_value_bounds {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup CSRMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : csrDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : CSRDecodedTrace trace setup) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
      (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
        (writeToken row.columns row.assignment port).word.Bounded) ∧
      (∀ token ∈ trace.terminalMemory, token.word.Bounded) :=
  NativeCSRRangeProofs.image_value_bounds image inputs accepted decoded

/-- Select the checked runtime pool without changing any native row or boundary.
    Every range follows initialization and actual CSR writes; no per-row range input. -/
theorem public_runtime_csr_value_bounds {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup CSRMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : csrDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (runtimeCSRData trace) before cells) (accepted : Accepted (runtimeCSRData trace))
    (decoded : CSRDecodedTrace trace setup) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
      (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
        (writeToken row.columns row.assignment port).word.Bounded) ∧
      (∀ token ∈ trace.terminalMemory, token.word.Bounded) :=
  NativeCSRRangeProofs.image_value_bounds (trace := runtimeCSRData trace) image inputs accepted decoded

end Airbender.ReducedMachine.Native
