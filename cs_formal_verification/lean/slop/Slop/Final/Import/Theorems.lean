module
public import Slop.Import.Json.Sound
public import Slop.Import.Json.Complete
public import Slop.Import.Json.Sample
public import Slop.Import.Decode.Schema

@[expose] public section

namespace Airbender.Json

/-- 1. The parser accepts only JSON texts without duplicate member names, and returns their value. -/
theorem parse_sound : ParseSoundClaim :=
  ⟨fun _ _ h => Parser.parse_sound' h, Parser.parse_sample, Parser.parse_duplicate⟩

/-- 2. A JSON text has exactly one value. -/
theorem text_unique : TextUniqueClaim :=
  ⟨fun _ _ _ hv hw => Parser.text_unique' hv hw, (Parser.parse_sound' Parser.parse_sample).1⟩

end Airbender.Json

namespace Airbender

/-- 3. The decoder returns exactly the circuit whose serde JSON is the value. -/
theorem decode_claim : DecodeClaim := Decode.Lawful.iff

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
