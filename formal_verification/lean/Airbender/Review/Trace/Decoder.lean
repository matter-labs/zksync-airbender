import Airbender.Proofs.Trace.DecoderSetup
import Airbender.Proofs.Mersenne31

namespace Airbender.Trace

/-- Public bytes and original Sail decoding construct the selected-profile setup.
    Accepted equations reject native minus-one padding; complete logical lookup
    membership then recovers an actual public instruction and its native fields.
    Rust setup-generation fidelity and cryptographic authentication remain separate. -/
theorem public_decoder_soundness {trace : Data mersenne31Modulus} {setup : DecoderSetup}
    {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    (image : decoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.Source before ∧ row.decoderQuery = entry.query :=
  Proofs.decoded_sources (by decide) image accepted decoded

end Airbender.Trace
