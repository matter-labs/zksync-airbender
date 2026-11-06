import Airbender.Proofs.Trace.Families.ReducedMachine.Values

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Public seed reads, actual fixed-pool native acceptance and original public
    shift decoding derive all native word ranges, including discarded reads/writes.
    No per-row value, clock, selector, range or expected read is supplied. -/
theorem public_shift_value_bounds {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ShiftMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary (fixedData trace) before cells) (accepted : Accepted (fixedData trace))
    (decoded : ShiftDecodedTrace (fixedData trace) setup) :
    (∀ row ∈ (fixedData trace).rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
      (∀ row ∈ (fixedData trace).rows, ∀ port ∈ row.ports,
        (writeToken row.columns row.assignment port).word.Bounded) ∧
      (∀ token ∈ (fixedData trace).terminalMemory, token.word.Bounded) :=
  NativeShiftRangeProofs.image_value_bounds image inputs accepted decoded

end Airbender.ReducedMachine.Native
