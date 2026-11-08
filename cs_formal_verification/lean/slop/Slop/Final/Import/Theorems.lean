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

end Airbender
