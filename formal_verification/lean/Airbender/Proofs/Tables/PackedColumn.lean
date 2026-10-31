import Airbender.Proofs.Tables.ImportedBlocks
import Airbender.Proofs.Tables.PackedBytes

namespace Airbender.Setup.Proofs.PackedColumn
set_option warningAsError true

def digit (packed index : Nat) : Nat := (packed / 256 ^ index) % 256

/-- Kernel arithmetic uses a primitive shift for large byte offsets. -/
def bytePower (count : Nat) : Nat := 1 <<< (8 * count)

theorem bytePower_eq (count : Nat) : bytePower count = 256 ^ count := by
  rw [bytePower, Nat.shiftLeft_eq]
  simp only [one_mul]
  rw [pow_mul]
  norm_num

theorem segment_digit (packed origin length index : Nat) (within : index < length) :
    digit ((packed / 256 ^ origin) % 256 ^ length) index =
      digit packed (origin + index) := by
  have splitPower : 256 ^ length = 256 ^ index * 256 ^ (length - index) := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt within)]
  have tailPower : 256 ^ (length - index) = 256 * 256 ^ (length - index - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ length - index)]
  simp only [digit]
  rw [splitPower, Nat.mod_mul_right_div_self, tailPower, Nat.mod_mul_right_mod,
    Nat.div_div_eq_div_mul, ← pow_add]


end Airbender.Setup.Proofs.PackedColumn
