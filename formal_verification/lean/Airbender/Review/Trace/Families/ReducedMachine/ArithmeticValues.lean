import Airbender.Proofs.Trace.Families.ReducedMachine.ArithmeticValues

namespace Airbender.ReducedMachine.Native
open Trace
set_option autoImplicit false

/-- Public seed reads, actual native acceptance with explicit modeled setup and original public
    arithmetic decoding derive all native word ranges, including discarded reads/writes.
    No per-row value, clock, selector, range or expected read is supplied. -/
theorem public_arithmetic_value_bounds {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ArithmeticMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : arithmeticDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : ArithmeticDecodedTrace trace setup) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
      (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
        (writeToken row.columns row.assignment port).word.Bounded) ∧
      (∀ token ∈ trace.terminalMemory, token.word.Bounded) :=
  NativeArithmeticRangeProofs.image_value_bounds image inputs accepted decoded

end Airbender.ReducedMachine.Native
