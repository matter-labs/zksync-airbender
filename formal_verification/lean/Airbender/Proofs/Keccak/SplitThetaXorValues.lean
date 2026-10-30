import Airbender.Proofs.Keccak.SplitThetaXorEntries
import Airbender.Proofs.Arithmetic.ByteAssembly

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup.LiteralTree Airbender.Arithmetic
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000

private theorem high_entry (node digit : Nat) (hn : node < 273) (hd : digit < 16) :
    (thetaRhoXor.columns[0]).entry node digit = xorByteHighEntry node digit :=
  xor_byte_high_entries ⟨node, hn⟩ ⟨digit, hd⟩

private theorem low_entry (node digit : Nat) (hn : node < 18) (hd : digit < 16) :
    (thetaRhoXor.columns[1]).entry node digit = xorByteLowEntry node digit :=
  xor_byte_low_entries ⟨node, hn⟩ ⟨digit, hd⟩

/-- Every actual first key is the high byte of the native row coordinate. -/
theorem xor_byte_high_value (row : Nat) :
    (thetaRhoXor.columns[0]).value row = row / 256 % 256 := by
  unfold Column.value
  rw [xor_byte_shapes.1.1, xor_byte_shapes.1.2]
  simp (disch := omega) only [Column.evaluate, high_entry, xorByteHighEntry, Nat.reducePow,
    Nat.div_one, if_pos, if_neg, ↓reduceIte, Nat.add_sub_cancel_left]
  omega

/-- Every actual second key is the low byte of the native row coordinate. -/
theorem xor_byte_low_value (row : Nat) :
    (thetaRhoXor.columns[1]).value row = row % 256 := by
  unfold Column.value
  rw [xor_byte_shapes.2.1.1, xor_byte_shapes.2.1.2]
  simp (disch := omega) only [Column.evaluate, low_entry, xorByteLowEntry, Nat.reducePow,
    Nat.div_one, if_pos, if_neg, ↓reduceIte, Nat.mul_zero, Nat.zero_add]
  omega

/-- The checked native byte-XOR transitions preserve their bounded node range. -/
theorem xor_byte_entry_bound {node digit : Nat} (hn : node < 256) (hd : digit < 16) :
    xorByteEntry node digit < 256 := by
  have high : node / 16 < 16 := by omega
  have paired := Nat.xor_lt_two_pow (n := 4) high hd
  have low : node % 16 < 16 := Nat.mod_lt _ (by decide)
  unfold xorByteEntry
  omega

private theorem output_entry (node digit : Nat) (hn : node < 256) (hd : digit < 16) :
    (thetaRhoXor.columns[2]).entry node digit = xorByteEntry node digit :=
  xor_byte_output_entries ⟨node, hn⟩ ⟨digit, hd⟩

private theorem output_chain {a b c d : Nat} (ha : a < 16) (hb : b < 16) (hc : c < 16) (_hd : d < 16) :
    xorByteEntry (xorByteEntry (xorByteEntry (xorByteEntry 0 a) b) c) d =
      16 * (a ^^^ c) + (b ^^^ d) := by
  have paired : a ^^^ c < 16 := Nat.xor_lt_two_pow (n := 4) ha hc
  have abmod : (16 * a + b) % 16 = b := by omega
  have abdiv : (16 * a + b) / 16 = a := by omega
  have bcmod : (16 * b + (a ^^^ c)) % 16 = a ^^^ c := by omega
  have bcdiv : (16 * b + (a ^^^ c)) / 16 = b := by omega
  simp only [xorByteEntry, Nat.zero_mod, Nat.zero_div, Nat.zero_xor, Nat.mul_zero, Nat.zero_add,
    Nat.mod_eq_of_lt ha, Nat.div_eq_of_lt ha, abmod, abdiv, bcmod, bcdiv]

/-- Every actual native output is the XOR of its complete corresponding byte keys. -/
theorem xor_byte_output_value (row : Nat) :
    (thetaRhoXor.columns[2]).value row = (row / 256 % 256) ^^^ (row % 256) := by
  have h3 : row / 4096 % 16 < 16 := Nat.mod_lt _ (by decide)
  have h2 : row / 256 % 16 < 16 := Nat.mod_lt _ (by decide)
  have h1 : row / 16 % 16 < 16 := Nat.mod_lt _ (by decide)
  have h0 : row % 16 < 16 := Nat.mod_lt _ (by decide)
  have n3 := xor_byte_entry_bound (by decide : 0 < 256) h3
  have n2 := xor_byte_entry_bound n3 h2
  have n1 := xor_byte_entry_bound n2 h1
  unfold Column.value
  rw [xor_byte_shapes.2.2.1, xor_byte_shapes.2.2.2]
  simp (disch := first | assumption | omega) only [Column.evaluate, output_entry,
    Nat.reducePow, Nat.div_one, ↓reduceIte]
  norm_num only
  simp only [ite_false]
  rw [output_chain h3 h2 h1 h0]
  have high : row / 256 % 256 = row / 256 % 16 + 16 * (row / 4096 % 16) := by omega
  have low : row % 256 = row % 16 + 16 * (row / 16 % 16) := by omega
  rw [high, low]
  have assembled := xor_of_chunks (width := 4) h2 h0
    (a₁ := row / 4096 % 16) (b₁ := row / 16 % 16)
  norm_num only [Nat.reducePow] at assembled
  omega

/-- The five actual padding columns retain their zero values for every row. -/
theorem xor_byte_padding_value (column : Fin 5) (row : Nat) :
    (thetaRhoXor.columns[3 + column.val]).value row = 0 := by
  have shape := xor_byte_padding_shapes column
  have entry (digit : Nat) (hd : digit < 16) := xor_byte_padding_entries column ⟨digit, hd⟩
  simp (disch := omega) [Column.value, shape.1, shape.2, Column.evaluate, entry]

/-- The actual discriminator stays equal to the native byte-XOR table ID. -/
theorem xor_byte_tag_value (row : Nat) : (thetaRhoXor.columns[8]).value row = 4 := by
  have entry (node digit : Nat) (hn : node < 4) (hd : digit < 16) :=
    xor_byte_tag_entries ⟨node, hn⟩ ⟨digit, hd⟩
  simp (disch := omega) [Column.value, xor_byte_tag_shape.1, xor_byte_tag_shape.2, Column.evaluate, entry]

end Airbender.Keccak.Split.Native.Fixed.Proofs
