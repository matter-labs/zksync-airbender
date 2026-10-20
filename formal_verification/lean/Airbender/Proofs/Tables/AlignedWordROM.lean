import Airbender.Review.Helpers.Tables.AlignedWordROM
import Airbender.Proofs.Mersenne31

namespace Airbender.Verification.AlignedWordROMProofs
set_option autoImplicit false

theorem values {p : Nat} [Fact p.Prime] (hp : 1048576 < p)
    {rom : WordROM} {key low high : ZMod p}
    (member : (romAlignedWordTable rom).Contains #[] #v[key,low,high]) :
    key.val < 1048576 ∧
      low = ((rom.word key.val).toNat % 65536 : Nat) ∧
      high = ((rom.word key.val).toNat / 65536 : Nat) := by
  change (∃ i : Fin 1048576, #v[key,low,high] = (rom.alignedRow i).map Nat.cast) at member
  obtain ⟨i, row⟩ := member
  have keyEq := congrArg (fun q => q[0]) row
  have lo := congrArg (fun q => q[1]) row
  have hi := congrArg (fun q => q[2]) row
  simp [WordROM.alignedRow] at keyEq lo hi
  have index : key.val = i.val := by
    rw [keyEq, ZMod.val_natCast_of_lt (by have := i.isLt; omega)]
  exact ⟨by rw [index]; exact i.isLt, by simpa only [index] using lo,
    by simpa only [index] using hi⟩

/-- The ordinary ROM model and aligned ROM model share the entire word value,
    including padding; only their address coordinate differs. -/
theorem byte_row (rom : WordROM) (i : Fin 1048576) :
    rom.row i = #v[4 * (rom.alignedRow i)[0],
      (rom.alignedRow i)[1],(rom.alignedRow i)[2]] := rfl

end Airbender.Verification.AlignedWordROMProofs
