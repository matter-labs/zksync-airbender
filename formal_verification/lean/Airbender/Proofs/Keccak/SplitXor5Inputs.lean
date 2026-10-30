import Airbender.Proofs.Keccak.SplitXor5Entries

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup.LiteralTree
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000

/-- Symbolic rows use only the checked finite native key transitions. -/
theorem xor5_key_entry (column : Fin 5) (node digit : Nat) (nodeBound : node < 20) (digitBound : digit < 16) :
    (columnParityXor5.columns[column.val]).entry node digit = xor5KeyEntry column node digit :=
  xor5_key_entries column ⟨node, nodeBound⟩ ⟨digit, digitBound⟩

/-- Each actual native key column is its corresponding bounded base-sixteen digit. -/
theorem xor5_key_values (column : Fin 5) (row : Nat) :
    (columnParityXor5.columns[column.val]).value row = row / 16 ^ column.val % 16 := by
  have shape := xor5_key_shapes column
  have entry := xor5_key_entry column
  unfold Column.value
  rw [shape.1, shape.2]
  fin_cases column
  all_goals
    simp (disch := omega) only [Column.evaluate, entry, xor5KeyEntry,
      Nat.reducePow, Nat.div_one, if_pos, if_neg, ↓reduceIte]

end Airbender.Keccak.Split.Native.Fixed.Proofs
