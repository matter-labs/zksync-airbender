module
public import Human.Import.TranscribeCommand

@[expose] public section

namespace Airbender.InitsTeardowns

-- The cached inits/teardowns file, transcribed in the shared form of the cached captures (trusted:
-- `Human/Import/TranscribeCommand.lean`), with its text and its bytes. No other claim reads this transcription.
import_circuit sharedLayoutCircuit from "../../cs/compiled_circuits/inits_and_teardowns_layout_gkr.json" bytes shared sharedLayoutCircuit

/-- The shared transcription of the cached file is what the parser and the decoder (fixed by `ParseSoundClaim`,
    `TextUniqueClaim` and `DecodeClaim`) make of the file's bytes: of the shared transcription, only the file read
    stays trusted. -/
def SharedBytesClaim : Prop :=
  (Json.parse sharedLayoutCircuitBytes >>= Circuit.decode) = .ok sharedLayoutCircuit

end Airbender.InitsTeardowns
