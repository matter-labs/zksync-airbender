import Airbender.Review.Helpers.Tables.WordROM
import Airbender.Review.Helpers.Memory.InitialImage

namespace Airbender.Verification
open Trace

/-- Actual public Sail word reads in increasing ROM order. The vector preserves
    the requested length without a witness-supplied size or value. -/
def readROMWords (before : Reference.RiscV.Sail.State) :
    (count : Nat) → Option (Vector (BitVec 32) count)
  | 0 => some #v[]
  | count + 1 => do
    let previous ← readROMWords before count
    let value ← match (Cell.ram (BitVec.ofNat 32 (4 * count))).read before with
      | .ok value _ => some value
      | .error _ _ => none
    pure (previous.push value)

/-- Read the public ROM prefix from actual Sail bytes. Reject excessive counts
    before reading; retain the complete native UNIMP tail in the resulting ROM.
    This constructor binds the readable prefix, not absent Sail padding bytes. -/
def wordROMImage (before : Reference.RiscV.Sail.State) (count : Nat) : Option WordROM :=
  if bound : count ≤ 1048576 then do
    let words ← readROMWords before count
    pure ⟨words.toList, by simpa using bound⟩
  else none

end Airbender.Verification
