import Airbender.Review.Helpers.Tables.WordROM

namespace Airbender.Verification

/-- Native proving-loader padding: retain supplied words and fill the remaining
    four-MiB image with zero. The raw table constructor's UNIMP fallback remains
    unchanged. This list model does not construct Sail bytes or prove Rust refinement. -/
def WordROM.zeroPadded (rom : WordROM) : WordROM where
  words := rom.words ++ List.replicate (1048576 - rom.words.length) 0
  capacity := by
    simp only [List.length_append, List.length_replicate]
    have := rom.capacity
    omega

end Airbender.Verification
