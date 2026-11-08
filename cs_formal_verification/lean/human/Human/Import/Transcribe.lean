module
public import Human.Import.Schema

@[expose] public section

/-! # TRUSTED: review. Bytes of an artifact JSON to its decoded value

This file and `TranscribeCommand.lean` are the trusted part of the import: what they compute is not
kernel-checked. Everything after them is: each artifact's `ArtifactImportClaim` states that the definitions the
claims use are the meaning functions (`Columns`, `Operations`, `InitsTeardownsLayout`) applied to the transcribed
artifact.

A circuit JSON is parsed by `Json.parse` (behaviour fixed by `ParseSoundClaim` and `TextUniqueClaim`,
`Human/Import/Theorems.lean`: it accepts exactly the JSON texts without duplicate member names) and decoded by the
`FromJson` instances derived for the serde mirror (`Schema.lean`). -/

namespace Airbender
open Lean

/-- The JSON value of a text, as a `Lean.Json` for the derived decoders. -/
def jsonOfText (text : String) : Except String Json :=
  Json.parse text

/-- The circuit artifact of a JSON text. -/
def parseCircuit (text : String) : Except String Circuit := do
  fromJson? (← jsonOfText text)

end Airbender
