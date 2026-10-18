import Airbender.Review.Helpers.Tables.WordROMImage
import Airbender.Review.Helpers.Tables.WordROMPadding
import Airbender.Review.Helpers.Memory.BytePadding

namespace Airbender.Verification
open Reference.RiscV.Sail

/-- Construct a native loader image from actual Sail prefix reads, then explicitly
    insert its zero padding into Sail byte memory. Missing prefix bytes and
    excessive lengths fail through `wordROMImage`; no expected ROM is supplied. -/
def paddedWordROMImage (before : State) (count : Nat) : Option (State × WordROM) := do
  let rom ← wordROMImage before count
  pure (paddedROMState before count, rom.zeroPadded)

end Airbender.Verification
