module
public import Human.Import.JsonGrammar
public import Human.Import.Exec.JsonParser

@[expose] public section

/-! # The artifact parser's claims

`parse` (Human/Import/Exec/JsonParser.lean, not reviewed) turns the pinned artifact bytes into a JSON value.
These claims fix its behaviour by the grammar of Human/Import/JsonGrammar.lean. -/

namespace Airbender.Json

/-- A small JSON text with every kind of value: null, true, false, a negative integer, a string with an escape,
    nested arrays and objects, and whitespace. -/
def sample : String := "{\"a\": [null, true, false, -12], \"b\": {\"c\": \"x\\n\", \"d\": [0, {}]}}"

/-- The value of `sample`. -/
def sampleValue : Value :=
  .obj [("a", .arr [.null, .bool true, .bool false, .int (-12)]),
        ("b", .obj [("c", .str "x\n"), ("d", .arr [.int 0, .obj []])])]

/-- A JSON text whose object has a duplicate member name. -/
def duplicate : String := "{\"a\":0,\"a\":0}"

/-- The parser accepts only JSON texts without duplicate member names and returns their value; in particular it
    rejects every malformed input and every input with a duplicate key. The sample shows acceptance is possible. -/
def ParseSoundClaim : Prop :=
  (∀ (bytes : ByteArray) (v : Value), parse bytes = .ok v → Text bytes.toList v ∧ NoDuplicateKeys v) ∧
  parse sample.toUTF8 = .ok sampleValue ∧ (parse duplicate.toUTF8).toBool = false

/-- A JSON text has exactly one value, so "the value of the bytes" is well defined. -/
def TextUniqueClaim : Prop :=
  (∀ (bytes : List UInt8) (v w : Value), Text bytes v → Text bytes w → v = w) ∧ Text (utf8 sample) sampleValue

end Airbender.Json
