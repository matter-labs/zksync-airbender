import Airbender.Proofs.Trace.Families.ShiftBinop.Values
import Airbender.Proofs.Mersenne31

namespace Airbender.ShiftBinop
set_option autoImplicit false
open Arithmetic Trace

/-- Public initialization, accepted native matching and full decoder membership
    derive all native word ranges, including discarded reads and masked shift/binop writes.
    No per-row value, clock, flag or expected-read premise is supplied. -/
theorem public_value_bounds {trace : Data mersenne31Modulus ShiftBinopFamily}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) :=
  Proofs.image_value_bounds image inputs accepted decoded

end Airbender.ShiftBinop
