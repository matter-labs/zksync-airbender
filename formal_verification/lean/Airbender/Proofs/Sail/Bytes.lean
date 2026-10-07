import SailRV32
import Mathlib.Tactic.IntervalCases
import Airbender.Proofs.Arithmetic.Bytes
namespace Airbender.Reference.Sail

set_option maxRecDepth 4096 in
/-- The original Sail byte loop, specialized to RV32. -/
theorem rev8_bytes (x : BitVec 32) : SailRV32.Functions.rev8 x =
    ((x.extractLsb' 0 8) ++ (x.extractLsb' 8 8)) ++
      ((x.extractLsb' 16 8) ++ (x.extractLsb' 24 8)) := by
  simp [SailRV32.Functions.rev8, SailRV32.Functions.zeros,
    ForIn.forIn, ForIn'.forIn', IntRange.forIn', IntRange.forIn'.loop,
    Membership.mem, Sail.BitVec.length]

  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_append
    (x := (x.extractLsb' 0 8) ++ (x.extractLsb' 8 8))
    (y := (x.extractLsb' 16 8) ++ (x.extractLsb' 24 8)),
    BitVec.getLsbD_append (x := x.extractLsb' 16 8) (y := x.extractLsb' 24 8),
    BitVec.getLsbD_append (x := x.extractLsb' 0 8) (y := x.extractLsb' 8 8)]
  interval_cases k <;> simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
      Sail.BitVec.extractLsb, BitVec.extractLsb]

/-- Numerical form used to assemble the circuit's four byte contributions. -/
theorem rev8_value (x : BitVec 32) :
    (SailRV32.Functions.rev8 x).toNat =
      16777216 * (x.extractLsb' 0 8).toNat + 65536 * (x.extractLsb' 8 8).toNat +
      256 * (x.extractLsb' 16 8).toNat + (x.extractLsb' 24 8).toNat := by
  have append_value {m n : Nat} (a : BitVec m) (b : BitVec n) :
      (a ++ b).toNat = a.toNat * 2 ^ n + b.toNat := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
  rw [rev8_bytes, append_value, append_value, append_value]
  norm_num
  ring

end Airbender.Reference.Sail
