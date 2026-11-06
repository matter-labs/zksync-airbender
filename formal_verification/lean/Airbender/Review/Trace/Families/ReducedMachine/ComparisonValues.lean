import Airbender.Proofs.Trace.Families.ReducedMachine.ComparisonValues

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Public seed reads, actual native acceptance at the exact fixed pool and original public
    comparison decoding derive all native word ranges, including discarded reads/writes.
    No per-row value, clock, selector, range or expected read is supplied. -/
theorem public_comparison_value_bounds {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ComparisonMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : comparisonDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : ComparisonDecodedTrace (fixedData trace) setup) :
    (∀ row ∈ (fixedData trace).rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
      (∀ row ∈ (fixedData trace).rows, ∀ port ∈ row.ports,
        (writeToken row.columns row.assignment port).word.Bounded) ∧
      (∀ token ∈ (fixedData trace).terminalMemory, token.word.Bounded) :=
  NativeComparisonRangeProofs.image_value_bounds image inputs accepted decoded

end Airbender.ReducedMachine.Native
