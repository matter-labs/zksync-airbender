import Airbender.Proofs.Trace.Families.WordMemory.Values
import Airbender.Proofs.Mersenne31

namespace Airbender.WordMemory
open Arithmetic Trace

/-- Public initialization, accepted native matching and full decoder membership
    derive all native word ranges, including discarded reads and masked writes.
    No per-row value, clock, flag or expected-read premise is supplied. -/
theorem public_value_bounds {trace : Data mersenne31Modulus WordMemoryFamily}
    {setup : DecoderSetup} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) :=
  Proofs.image_value_bounds (by decide) inputs accepted decoded

end Airbender.WordMemory
