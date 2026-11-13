module
public import Human.Import.JsonGrammar
public import Human.Import.Exec.JsonParser
public import Human.Import.Exec.Decode
public import Human.Import.Coefficients

@[expose] public section

/-! # The artifact parser's and decoder's claims

`parse` (Human/Import/Exec/JsonParser.lean, not reviewed) turns the pinned artifact bytes into a JSON value; the
first two claims fix its behaviour by the grammar of Human/Import/JsonGrammar.lean. `Circuit.decode`
(Human/Import/Exec/Decode.lean, not reviewed) turns that value into a `Circuit`; `DecodeClaim` fixes its behaviour
by the JSON serde writes for a circuit (`Serde.encode`, Human/Import/Serde.lean and Schema.lean). -/

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

namespace Airbender

/-- The decoder returns `c` from a JSON value exactly when the value is the one serde writes for `c`. So a value
    decodes to at most one circuit (`encode` is injective), and every value serde writes for a circuit decodes. -/
def DecodeClaim : Prop := ∀ (v : Json.Value) (c : Circuit), Circuit.decode v = .ok c ↔ Serde.encode c = v

/-- The field constants of the spec and the importer: `montgomeryInverse` (`RV.RINV`) is `2^-32` mod BabyBear, the
    serialized coefficients of 1 and -1 decode to 1 and -1, and a coefficient's small signed representative
    (`Artifact.signedCoefficient`) is its canonical residue in every ring of characteristic BabyBear. -/
def ConstantsClaim : Prop :=
  2 ^ 32 * montgomeryInverse % babyBearModulus = 1 ∧
  (Coefficient.mk ⟨268435454, by decide⟩).canonical = Fp.one ∧
  (Coefficient.mk ⟨1744830467, by decide⟩).canonical.val = babyBearModulus - 1 ∧
  ∀ {F : Type} [CommRing F] [CharP F babyBearModulus] (c : Coefficient),
    (Artifact.signedCoefficient c : F) = (c.canonical.val : F)

end Airbender
