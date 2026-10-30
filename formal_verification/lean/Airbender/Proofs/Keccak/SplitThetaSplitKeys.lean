import Airbender.Proofs.Keccak.SplitThetaSplitEntries

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup.LiteralTree
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false

private theorem first_entry (node digit : Nat) (hn : node < 18) (hd : digit < 16) :
    (thetaRhoXorSplit.columns[0]).entry node digit = xorByteLowEntry node digit :=
  theta_split_first_entries ⟨node, hn⟩ ⟨digit, hd⟩

private theorem second_entry (node digit : Nat) (hn : node < 273) (hd : digit < 16) :
    (thetaRhoXorSplit.columns[1]).entry node digit = xorByteHighEntry node digit :=
  theta_split_second_entries ⟨node, hn⟩ ⟨digit, hd⟩

/-- Every actual first key is the low byte of its native row coordinate. -/
theorem theta_split_first_value (row : Fin thetaRhoXorSplit.length) :
    (thetaRhoXorSplit.columns[0]).value row.val = row.val % 256 := by
  have bound : row.val < 524288 := row.isLt
  have shiftBound : row.val / 65536 % 16 < 8 := by omega
  have root := (theta_split_key_roots ⟨row.val / 65536 % 16, shiftBound⟩).1
  unfold Column.value
  rw [theta_split_key_shapes.1.1, theta_split_key_shapes.1.2]
  change (thetaRhoXorSplit.columns[0]).evaluate 4
    ((thetaRhoXorSplit.columns[0]).entry 20 (row.val / 65536 % 16)) row.val = _
  rw [root]
  simp (disch := omega) only [Column.evaluate, first_entry, xorByteLowEntry, Nat.reducePow,
    Nat.div_one, if_pos, if_neg, ↓reduceIte, Nat.mul_zero, Nat.zero_add]
  omega

/-- Every actual second key is the next byte of its native row coordinate. -/
theorem theta_split_second_value (row : Fin thetaRhoXorSplit.length) :
    (thetaRhoXorSplit.columns[1]).value row.val = row.val / 256 % 256 := by
  have bound : row.val < 524288 := row.isLt
  have shiftBound : row.val / 65536 % 16 < 8 := by omega
  have root := (theta_split_key_roots ⟨row.val / 65536 % 16, shiftBound⟩).2.1
  unfold Column.value
  rw [theta_split_key_shapes.2.1.1, theta_split_key_shapes.2.1.2]
  change (thetaRhoXorSplit.columns[1]).evaluate 4
    ((thetaRhoXorSplit.columns[1]).entry 273 (row.val / 65536 % 16)) row.val = _
  rw [root]
  simp (disch := omega) only [Column.evaluate, second_entry, xorByteHighEntry, Nat.reducePow,
    Nat.div_one, if_pos, if_neg, ↓reduceIte, Nat.add_sub_cancel_left]
  omega

/-- Every actual third key is the native shift in the range zero through seven. -/
theorem theta_split_shift_value (row : Fin thetaRhoXorSplit.length) :
    (thetaRhoXorSplit.columns[2]).value row.val = row.val / 65536 := by
  have bound : row.val < 524288 := row.isLt
  have shiftBound : row.val / 65536 < 8 := by omega
  have selected : row.val / 65536 % 16 = row.val / 65536 := by omega
  have root := (theta_split_key_roots ⟨row.val / 65536, shiftBound⟩).2.2
  have entry (digit : Nat) (hd : digit < 16) :=
    theta_split_shift_entries ⟨row.val / 65536, shiftBound⟩ ⟨digit, hd⟩
  unfold Column.value
  rw [theta_split_key_shapes.2.2.1, theta_split_key_shapes.2.2.2]
  change (thetaRhoXorSplit.columns[2]).evaluate 4
    ((thetaRhoXorSplit.columns[2]).entry 8 (row.val / 65536 % 16)) row.val = _
  rw [selected, root]
  simp (disch := omega) [Column.evaluate, entry]

/-- Every actual padding value stays zero on the complete native domain. -/
theorem theta_split_padding_value (column : Fin 3) (row : Nat) :
    (thetaRhoXorSplit.columns[5 + column.val]).value row = 0 := by
  have shape := theta_split_padding_shapes column
  have entry (digit : Nat) (hd : digit < 16) := theta_split_padding_entries column ⟨digit, hd⟩
  simp (disch := omega) [Column.value, shape.1, shape.2, Column.evaluate, entry]

/-- Every actual discriminator value is the native XOR/split table ID. -/
theorem theta_split_tag_value (row : Fin thetaRhoXorSplit.length) :
    (thetaRhoXorSplit.columns[8]).value row.val = 58 := by
  have bound : row.val < 524288 := row.isLt
  have shiftBound : row.val / 65536 % 16 < 8 := by omega
  have root := theta_split_tag_roots ⟨row.val / 65536 % 16, shiftBound⟩
  have entry (node digit : Nat) (hn : node < 4) (hd : digit < 16) :=
    theta_split_tag_entries ⟨node, hn⟩ ⟨digit, hd⟩
  unfold Column.value
  rw [theta_split_tag_shape.1, theta_split_tag_shape.2]
  change (thetaRhoXorSplit.columns[8]).evaluate 4
    ((thetaRhoXorSplit.columns[8]).entry 5 (row.val / 65536 % 16)) row.val = _
  rw [root]
  simp (disch := omega) [Column.evaluate, entry]

end Airbender.Keccak.Split.Native.Fixed.Proofs
