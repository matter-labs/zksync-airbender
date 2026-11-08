module
public import Human.Import.Schema
public import Human.Import.Exec.JsonParser

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

mutual
/-- A JSON value as a `Lean.Json`, the input of the derived decoders. Integers become `JsonNumber`s with
    exponent 0; an object becomes a map from member names (unique, by `ParseSoundClaim`) to values. -/
def Json.Value.toLean : Json.Value → Lean.Json
  | .null => .null
  | .bool b => .bool b
  | .int n => .num (JsonNumber.fromInt n)
  | .str s => .str s
  | .arr items => .arr (Json.Value.itemsToLean items).toArray
  | .obj members => Lean.Json.mkObj (Json.Value.membersToLean members)

/-- `toLean` of each item. -/
def Json.Value.itemsToLean : List Json.Value → List Lean.Json
  | [] => []
  | v :: vs => v.toLean :: Json.Value.itemsToLean vs

/-- `toLean` of each member's value. -/
def Json.Value.membersToLean : List (String × Json.Value) → List (String × Lean.Json)
  | [] => []
  | (k, v) :: ms => (k, v.toLean) :: Json.Value.membersToLean ms
end

/-- The JSON value of a text: `Json.parse` (behaviour fixed by `ParseSoundClaim` and `TextUniqueClaim`), as a
    `Lean.Json`. -/
def jsonOfText (text : String) : Except String Lean.Json :=
  return (← Json.parse text.toUTF8).toLean

/-- The circuit artifact of a JSON text. -/
def parseCircuit (text : String) : Except String Circuit := do
  fromJson? (← jsonOfText text)

end Airbender
