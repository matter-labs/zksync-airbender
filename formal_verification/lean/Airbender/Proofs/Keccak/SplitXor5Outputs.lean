import Airbender.Proofs.Keccak.SplitXor5Inputs

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup.LiteralTree
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000

/-- Symbolic output rows use only the checked native literal transitions. -/
theorem xor5_output_entry (node digit : Nat) (nodeBound : node < 16) (digitBound : digit < 16) :
    (columnParityXor5.columns[5]).entry node digit = node ^^^ digit :=
  xor5_output_entries ⟨node, nodeBound⟩ ⟨digit, digitBound⟩

/-- Every actual native output is XOR of its five corresponding input nibbles. -/
theorem xor5_output_value (row : Nat) : (columnParityXor5.columns[5]).value row =
    row % 16 ^^^ (row / 16 % 16) ^^^ (row / 256 % 16) ^^^ (row / 4096 % 16) ^^^ (row / 65536 % 16) := by
  have h4 : row / 65536 % 16 < 16 := Nat.mod_lt _ (by decide)
  have h3 : row / 4096 % 16 < 16 := Nat.mod_lt _ (by decide)
  have h2 : row / 256 % 16 < 16 := Nat.mod_lt _ (by decide)
  have h1 : row / 16 % 16 < 16 := Nat.mod_lt _ (by decide)
  have h43 : (row / 65536 % 16) ^^^ (row / 4096 % 16) < 16 := Nat.xor_lt_two_pow (n := 4) h4 h3
  have h432 : ((row / 65536 % 16) ^^^ (row / 4096 % 16)) ^^^ (row / 256 % 16) < 16 :=
    Nat.xor_lt_two_pow (n := 4) h43 h2
  have h4321 : (((row / 65536 % 16) ^^^ (row / 4096 % 16)) ^^^ (row / 256 % 16)) ^^^
      (row / 16 % 16) < 16 := Nat.xor_lt_two_pow (n := 4) h432 h1
  unfold Column.value
  rw [xor5_output_shape.1, xor5_output_shape.2]
  simp (disch := first | assumption | omega) only [Column.evaluate, xor5_output_entry,
    Nat.reducePow, Nat.div_one, Nat.zero_xor, ↓reduceIte]
  ac_rfl

/-- Check the actual native padding and discriminator node values. -/
theorem xor5_fixed_entries : ∀ (node : Fin 5) (digit : Fin 16),
    (columnParityXor5.columns[6]).entry 0 digit.val = 0 ∧
      (columnParityXor5.columns[7]).entry node.val digit.val = if node.val = 0 then 64 else node.val - 1 := by
  decide +kernel

/-- The actual native row retains the zero padding field and discriminator 64. -/
theorem xor5_fixed_values (row : Nat) : (columnParityXor5.columns[6]).value row = 0 ∧
    (columnParityXor5.columns[7]).value row = 64 := by
  have padding (digit : Nat) (bound : digit < 16) := (xor5_fixed_entries 0 ⟨digit, bound⟩).1
  have tag (node digit : Nat) (nodeBound : node < 5) (digitBound : digit < 16) :=
    (xor5_fixed_entries ⟨node, nodeBound⟩ ⟨digit, digitBound⟩).2
  have padShape : (columnParityXor5.columns[6]).depth = 5 ∧ (columnParityXor5.columns[6]).root = 0 :=
    ⟨rfl, rfl⟩
  have tagShape : (columnParityXor5.columns[7]).depth = 5 ∧ (columnParityXor5.columns[7]).root = 4 :=
    ⟨rfl, rfl⟩
  simp (disch := omega) [Column.value, padShape.1, padShape.2, tagShape.1, tagShape.2,
    Column.evaluate, padding, tag]

end Airbender.Keccak.Split.Native.Fixed.Proofs
