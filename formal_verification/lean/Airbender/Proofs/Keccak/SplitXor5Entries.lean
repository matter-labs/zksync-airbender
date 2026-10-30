import Airbender.Data.Setup.Keccak.ColumnParityXor5
import Mathlib.Tactic.FinCases

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup.LiteralTree
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000

/-- A compact normal form of the actual native key-column literal transitions. -/
def xor5KeyEntry (column : Fin 5) (node digit : Nat) : Nat :=
  if column.val = 0 then
    if node = 0 then digit else if node < 5 then node - 1 else 0
  else if node < 16 then node else if node = 16 then digit
  else if node < 21 - column.val then node - 1 else 0

theorem xor5_key_shapes : ∀ column : Fin 5,
    (columnParityXor5.columns[column.val]).depth = 5 ∧
      (columnParityXor5.columns[column.val]).root = if column.val = 0 then 4 else 20 - column.val := by
  intro column
  fin_cases column <;> exact ⟨rfl, rfl⟩

/-- Check every key-column transition against the emitted native literal nodes. -/
theorem xor5_key_entries : ∀ (column : Fin 5) (node : Fin 20) (digit : Fin 16),
    (columnParityXor5.columns[column.val]).entry node.val digit.val = xor5KeyEntry column node.val digit.val := by
  decide +kernel

/-- The actual output has five literal levels and its original root node. -/
theorem xor5_output_shape : (columnParityXor5.columns[5]).depth = 5 ∧
    (columnParityXor5.columns[5]).root = 0 := by exact ⟨rfl, rfl⟩

/-- All 256 output-node transitions are actual retained nibble-XOR literals. -/
theorem xor5_output_entries : ∀ (node digit : Fin 16),
    (columnParityXor5.columns[5]).entry node.val digit.val = node.val ^^^ digit.val := by
  decide +kernel

end Airbender.Keccak.Split.Native.Fixed.Proofs
