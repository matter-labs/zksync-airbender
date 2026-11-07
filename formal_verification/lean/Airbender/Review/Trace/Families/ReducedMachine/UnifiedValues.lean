import Airbender.Proofs.Trace.Families.ReducedMachine.UnifiedValues

namespace Airbender.ReducedMachine.Native
open Trace NativeShadow
set_option autoImplicit false

/-- Public seed reads, actual native acceptance with the exact native fixed pool and original public
    unified seven-profile decoding derive all native word ranges, including discarded reads/writes.
    No per-row value, clock, selector, range or expected read is supplied. -/
theorem public_unified_value_bounds {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup UnifiedMode} {before : Reference.RiscV.Sail.State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage before count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) before cells seeds) (accepted : Accepted (fixedData trace))
    (decoded : UnifiedDecodedTrace (fixedData trace) setup) :
    (∀ row ∈ (fixedData trace).rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
      (∀ row ∈ (fixedData trace).rows, ∀ port ∈ row.ports,
        (writeToken row.columns row.assignment port).word.Bounded) ∧
      (∀ token ∈ (fixedData trace).terminalMemory, token.word.Bounded) :=
  NativeUnifiedRangeProofs.image_value_bounds image inputs accepted decoded

end Airbender.ReducedMachine.Native
