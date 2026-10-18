import Airbender.Proofs.Tables.NativeDecoder

namespace Airbender.Verification.NativeSetup

/-- Full active setup membership equals the actual regional export's membership.
    Native padding is retained; normalization/LDE and argument enforcement remain separate. -/
theorem native_decoder_membership (kind : DecoderKind) (query : Vector (ZMod mersenne31Modulus) 10) :
    DecoderContains kind query ↔ ∃ i : Fin 1048576, query = decoderPrefixRow kind i :=
  Proofs.decoder_membership kind query

end Airbender.Verification.NativeSetup
