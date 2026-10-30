import Airbender.Proofs.Keccak.SplitChiCallAddresses

namespace Airbender.Keccak.Split.Native.Proofs
open Arithmetic Trace
set_option warningAsError true
set_option maxHeartbeats 1600000

/-- Two bounded low limbs separate the low and high thirty-two-bit lane halves. -/
theorem chi5_four_limb_halves {a b c d : Nat} (ha : a < 65536) (hb : b < 65536) (high : Bool) :
    Call.half (a + 65536 * (b + 65536 * (c + 65536 * d))) high =
      (if high then Word.mk c d else Word.mk a b).toBitVec := by
  have low : a + 65536 * b < 4294967296 := by omega
  have packed : a + 65536 * (b + 65536 * (c + 65536 * d)) =
      a + 65536 * b + 4294967296 * (c + 65536 * d) := by ring
  cases high <;> simp only [Call.half, Bool.false_eq_true, ↓reduceIte, Word.toBitVec, Word.value, limbBase]
  all_goals apply BitVec.eq_of_toNat_eq
  all_goals simp only [BitVec.toNat_ofNat, Nat.reducePow]
  all_goals rw [packed]
  all_goals omega

variable [Fact babyBearModulus.Prime]

/-- Both native lane ports store the exact reference half-word values. -/
theorem chi5_lane_port_half (cached writing high : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then Chi5Cached.clockConstraints chi5FixedTable else Chi5.clockConstraints chi5FixedTable))
    (lane : Fin 5) :
    Call.half (chi5LaneValue cached writing w lane) high = memoryWord
      (if writing then (chi5LanePort cached lane high).writeCode w else (chi5LanePort cached lane high).readCode w) := by
  rw [chi5_lane_port_values]
  unfold memoryWord
  rw [Nat.unpair_pair]
  have low := (chi5_lane_limb_value cached writing w holds lane 0).1
  have next := (chi5_lane_limb_value cached writing w holds lane 1).1
  cases high
  · exact chi5_four_limb_halves low next false
  · exact chi5_four_limb_halves low next true

end Airbender.Keccak.Split.Native.Proofs
