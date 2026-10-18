import Airbender.Import.SetupEmbed
import Airbender.Review.Helpers.Tables.WordROM

namespace Airbender.WordMemory.Native
open Airbender.Setup

import_native_setup exported from "artifacts/setup/word-memory-native.json"

/-- The original public input words retained verbatim in this native fixture. -/
def programROM : Verification.WordROM :=
  ⟨[0x0100a183, 0x0030a823, 0x0100a003, 0xc0001073], by decide⟩

end Airbender.WordMemory.Native
