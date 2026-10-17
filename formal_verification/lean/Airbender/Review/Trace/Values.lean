import Airbender.Proofs.Mersenne31
import Airbender.Proofs.Trace.Values

namespace Airbender.Trace

/-- Public Sail seeds, accepted native history and complete decoder membership
    derive every read, actual write and terminal word bound. No per-row bounds,
    mask answers or expected memory values are supplied. Setup generation and
    cryptographic membership enforcement remain separate boundaries. -/
theorem public_image_value_bounds {trace : Data mersenne31Modulus} {setup : DecoderSetup}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) :=
  Proofs.image_value_bounds (by decide) inputs accepted decoded

end Airbender.Trace
