import Airbender.Proofs.AddSub.NativeSetup

namespace Airbender.AddSub
open Trace

/-- Actual native export membership and accepted arithmetic constraints recover
    original public Sail bytes and decoding, excluding the interior hole and tail. -/
theorem exported_decoder_soundness {row : Row mersenne31Modulus}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints ()))
    (member : ∃ i : Fin 1048576, row.decoderQuery = NativeSetup.arithmeticDecoder.row i) :
    ∃ entry ∈ NativeSetup.setup.program,
      entry.Source NativeSetup.before ∧ row.decoderQuery = entry.query :=
  Proofs.native_exported_source constraints member

end Airbender.AddSub
