import Airbender.Data.Setup.Keccak.ThetaRhoXor
import Mathlib.Tactic.FinCases

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup.LiteralTree
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000

/-- Normal form of the actual high-byte key transitions. -/
def xorByteHighEntry (node digit : Nat) : Nat :=
  if node < 256 then node else if node < 272 then 16 * (node - 256) + digit
  else if node = 272 then 256 + digit else 0

/-- Normal form of the actual low-byte key transitions. -/
def xorByteLowEntry (node digit : Nat) : Nat :=
  if node < 16 then 16 * node + digit else if node = 16 then 0 else if node = 17 then 16 else 0

/-- Normal form of the actual byte-XOR literal transitions. -/
def xorByteEntry (node digit : Nat) : Nat := 16 * (node % 16) + (node / 16 ^^^ digit)

/-- The three arithmetic columns retain their native depths and roots. -/
theorem xor_byte_shapes :
    ((thetaRhoXor.columns[0]).depth = 4 ∧ (thetaRhoXor.columns[0]).root = 272) ∧
      ((thetaRhoXor.columns[1]).depth = 4 ∧ (thetaRhoXor.columns[1]).root = 17) ∧
      ((thetaRhoXor.columns[2]).depth = 4 ∧ (thetaRhoXor.columns[2]).root = 0) := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Check every actual high-byte key transition. -/
theorem xor_byte_high_entries : ∀ (node : Fin 273) (digit : Fin 16),
    (thetaRhoXor.columns[0]).entry node.val digit.val = xorByteHighEntry node.val digit.val := by
  decide +kernel

/-- Check every actual low-byte key transition. -/
theorem xor_byte_low_entries : ∀ (node : Fin 18) (digit : Fin 16),
    (thetaRhoXor.columns[1]).entry node.val digit.val = xorByteLowEntry node.val digit.val := by
  decide +kernel

/-- Check every actual byte-XOR transition against its two bounded nibbles. -/
theorem xor_byte_output_entries : ∀ (node : Fin 256) (digit : Fin 16),
    (thetaRhoXor.columns[2]).entry node.val digit.val = xorByteEntry node.val digit.val := by
  decide +kernel

/-- The five physical padding columns retain their native zero nodes. -/
theorem xor_byte_padding_shapes : ∀ column : Fin 5,
    (thetaRhoXor.columns[3 + column.val]).depth = 4 ∧
      (thetaRhoXor.columns[3 + column.val]).root = 0 := by
  intro column
  fin_cases column <;> exact ⟨rfl, rfl⟩

theorem xor_byte_padding_entries : ∀ (column : Fin 5) (digit : Fin 16),
    (thetaRhoXor.columns[3 + column.val]).entry 0 digit.val = 0 := by
  decide +kernel

/-- The physical discriminator retains its original four-level literal chain. -/
theorem xor_byte_tag_shape : (thetaRhoXor.columns[8]).depth = 4 ∧
    (thetaRhoXor.columns[8]).root = 3 := by exact ⟨rfl, rfl⟩

theorem xor_byte_tag_entries : ∀ (node : Fin 4) (digit : Fin 16),
    (thetaRhoXor.columns[8]).entry node.val digit.val = if node.val = 0 then 4 else node.val - 1 := by
  decide +kernel

end Airbender.Keccak.Split.Native.Fixed.Proofs
