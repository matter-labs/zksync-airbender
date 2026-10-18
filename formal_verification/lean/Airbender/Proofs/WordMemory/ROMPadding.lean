import Airbender.Review.Helpers.Tables.WordROMPadding

namespace Airbender.WordMemory.Proofs
open Verification

/-- The modeled proving-loader image covers the entire native ROM region. -/
theorem zero_padding_length (rom : WordROM) : rom.zeroPadded.words.length = 1048576 := by
  simp only [WordROM.zeroPadded, List.length_append, List.length_replicate]
  have := rom.capacity
  omega

/-- Padding retains every supplied public program word. -/
theorem zero_padding_prefix (rom : WordROM) {index : Nat} (bound : index < rom.words.length) :
    rom.zeroPadded.word index = rom.word index := by
  simp [WordROM.word, WordROM.zeroPadded, List.getElem?_append, bound]

/-- Every supplied-image tail slot is zero, independently of UNIMP fallback. -/
theorem zero_padding_tail (rom : WordROM) {index : Nat}
    (start : rom.words.length ≤ index) (bound : index < 1048576) :
    rom.zeroPadded.word index = 0 := by
  have tail : index - rom.words.length < 1048576 - rom.words.length := by omega
  simp [WordROM.word, WordROM.zeroPadded, List.getElem?_append, Nat.not_lt.mpr start, tail]

end Airbender.WordMemory.Proofs
