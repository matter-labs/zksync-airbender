module
public import Proven.Import.Json.Sound
public import Proven.Import.Json.Complete
public import Proven.Import.Json.Sample
public import Proven.Import.Decode.Schema
public import Human.Circuits.AddSub.Artifact

@[expose] public section

namespace Airbender.Json

/-- 1. The parser accepts only JSON texts without duplicate member names, and returns their value. -/
theorem parse_sound : ParseSoundClaim :=
  fun _ _ h => Parser.parse_sound' h

/-- 2. A JSON text has exactly one value. -/
theorem text_unique : TextUniqueClaim :=
  fun _ _ _ hv hw => Parser.text_unique' hv hw

/-- The parser accepts the sample and rejects its duplicate-key case. -/
theorem parse_sound_satisfiable : ParseSoundSatisfiableClaim :=
  ⟨sample.toUTF8, sampleValue, Parser.parse_sample, rfl, rfl, Parser.parse_duplicate⟩

/-- The grammar has both sample derivations that the uniqueness claim requires. -/
theorem text_unique_satisfiable : TextUniqueSatisfiableClaim :=
  ⟨utf8 sample, sampleValue, sampleValue, (Parser.parse_sound' Parser.parse_sample).1,
    (Parser.parse_sound' Parser.parse_sample).1, rfl, rfl⟩

end Airbender.Json

namespace Airbender

/-- 3. The decoder returns exactly the circuit whose serde JSON is the value. -/
theorem decode_claim : DecodeClaim := Decode.Lawful.iff

/-- The decoder accepts the serde value of the imported ADD/SUB circuit. -/
theorem decode_satisfiable : DecodeSatisfiableClaim :=
  ⟨Serde.encode AddSub.importedCircuit, AddSub.importedCircuit, (decode_claim _ _).mpr rfl⟩

private theorem signedCoefficient_mod (c : Coefficient) :
    Artifact.signedCoefficient c % (babyBearModulus : Int) = c.canonical.val := by
  have hb := c.canonical.isLt
  unfold Artifact.signedCoefficient
  dsimp only
  split
  · exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast hb)
  · rw [Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod]
    exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast hb)

private theorem signedCoefficient_cast {F : Type} [CommRing F] [CharP F babyBearModulus]
    (c : Coefficient) : (Artifact.signedCoefficient c : F) = (c.canonical.val : F) := by
  rw [CharP.intCast_eq_intCast_mod F babyBearModulus (a := Artifact.signedCoefficient c),
    signedCoefficient_mod, Int.cast_natCast]

/-- 4. The field constants. -/
theorem constants_claim : ConstantsClaim :=
  ⟨by decide, by decide, by decide, fun c => signedCoefficient_cast c⟩

end Airbender
