module
public import Human.Import.Exec.Decode

@[expose] public section

/-! # TRUSTED: review. Bytes of an artifact JSON to its decoded value

This file and `TranscribeCommand.lean` are the trusted part of the import: what they compute is not
kernel-checked. Everything after them is: each artifact's `ArtifactImportClaim` states that the definitions the
claims use are the meaning functions (`Columns`, `Operations`, `InitsTeardownsLayout`) applied to the transcribed
artifact.

A circuit JSON is parsed by `Json.parse` (behaviour fixed by `ParseSoundClaim` and `TextUniqueClaim`: it accepts
exactly the JSON texts without duplicate member names) and decoded by `Circuit.decode` (behaviour fixed by
`DecodeClaim`: it returns the circuit whose `Serde.encode` is the value), all in `Human/Import/Theorems.lean`. What
remains trusted here is reading the file and the composition of the two. -/

namespace Airbender

/-- The circuit artifact of a JSON text. -/
def parseCircuit (text : String) : Except String Circuit := do
  Circuit.decode (← Json.parse text.toUTF8)

end Airbender
