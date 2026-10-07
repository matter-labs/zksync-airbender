import Airbender.Proofs.ShiftBinop.Lookups

namespace Airbender.Verification
open Airbender.Arithmetic

-- Algebraic helpers for combining lookup outputs; Sail remains the ISA spec.
def shiftOperation (tag : Nat) (x : BitVec 32) (amount : Nat) : BitVec 32 :=
  if tag = 1 then x.shiftLeft amount else if tag = 2 then x.ushiftRight amount
  else x.sshiftRight amount

theorem shift_contributions_value (tag : Nat) (valid : tag = 1 ∨ tag = 2 ∨ tag = 3)
    (x : BitVec 32) (amount : Nat) :
    (shiftOperation tag x amount).toNat =
      (shiftByteContribution 0 (x.extractLsb' 0 8).toNat amount tag).toNat +
      (shiftByteContribution 1 (x.extractLsb' 8 8).toNat amount tag).toNat +
      (shiftByteContribution 2 (x.extractLsb' 16 8).toNat amount tag).toNat +
      (shiftByteContribution 3 (x.extractLsb' 24 8).toNat amount tag).toNat := by
  have chunk (i : Fin 4) : byteChunk x i =
      (BitVec.ofNat 32 (x.extractLsb' (8 * i.val) 8).toNat).shiftLeft (8 * i.val) := by
    unfold byteChunk
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by have := (x.extractLsb' (8 * i.val) 8).isLt; omega)).symm
  rcases valid with rfl | rfl | rfl
  · simpa [shiftOperation, shiftByteContribution, chunk] using shiftLeft_chunks_value x amount
  · simpa [shiftOperation, shiftByteContribution, chunk] using ushiftRight_chunks_value x amount
  · simpa [shiftOperation, shiftByteContribution, chunk] using sshiftRight_chunks_value x amount

/-- Low-byte truncation equals the architectural low-five-bit amount. -/
theorem low_byte_shift_amount (x : BitVec 32) :
    (x.extractLsb' 0 8).toNat % 32 = (x.extractLsb' 0 5).toNat := by
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  norm_num only [Nat.reducePow, Nat.div_one]
  exact Nat.mod_mod_of_dvd _ (by decide)

end Airbender.Verification
