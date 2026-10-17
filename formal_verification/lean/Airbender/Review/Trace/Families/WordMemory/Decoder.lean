import Airbender.Proofs.Trace.Families.WordMemory.Decoder
import Airbender.Proofs.Mersenne31

namespace Airbender.WordMemory
open Trace

/-- Public LW/SW bytes and original Sail decoding, recovered from complete native
    padded membership. Native equations reject padding; initialized word-memory
    history, ROM-byte binding and instruction execution remain separate. -/
theorem public_decoder_soundness {trace : Data mersenne31Modulus WordMemoryFamily}
    {setup : DecoderSetup} {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}
    (image : decoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.SourceWith before decoderFields ∧ row.decoderQuery = entry.query :=
  Proofs.decoded_sources (by decide) image accepted decoded

end Airbender.WordMemory
