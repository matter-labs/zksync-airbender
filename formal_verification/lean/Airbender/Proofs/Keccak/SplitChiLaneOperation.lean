import Airbender.Proofs.Keccak.SplitChiLimbOperation

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxHeartbeats 1600000

/-- The actual four native memory limbs form one sixty-four-bit lane. -/
def chi5LaneValue (cached writing : Bool) (w : Nat → ZMod babyBearModulus) (lane : Fin 5) : Nat :=
  (chi5LaneLimb cached writing w lane 0).val + 65536 *
    ((chi5LaneLimb cached writing w lane 1).val + 65536 *
      ((chi5LaneLimb cached writing w lane 2).val + 65536 * (chi5LaneLimb cached writing w lane 3).val))

variable [Fact babyBearModulus.Prime]

/-- All actual chi5 read and write lanes have canonical sixty-four-bit values. -/
theorem chi5_lane_bound (cached writing : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then Chi5Cached.clockConstraints chi5FixedTable else Chi5.clockConstraints chi5FixedTable))
    (lane : Fin 5) : chi5LaneValue cached writing w lane < 2 ^ 64 := by
  have h0 := (chi5_lane_limb_value cached writing w holds lane 0).1
  have h1 := (chi5_lane_limb_value cached writing w holds lane 1).1
  have h2 := (chi5_lane_limb_value cached writing w holds lane 2).1
  have h3 := (chi5_lane_limb_value cached writing w holds lane 3).1
  unfold chi5LaneValue
  norm_num only [Nat.reducePow]
  omega

/-- Both native cache modes enforce chi on each complete actual memory lane. -/
theorem chi5_native_lane_operation (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then Chi5Cached.clockConstraints chi5FixedTable else Chi5.clockConstraints chi5FixedTable))
    (lane : Fin 5) :
    chi5LaneValue cached true w lane = chi5LaneValue cached false w lane ^^^
      (not64 (chi5LaneValue cached false w ⟨(lane.val + 1) % 5, Nat.mod_lt _ (by decide)⟩) &&&
        chi5LaneValue cached false w ⟨(lane.val + 2) % 5, Nat.mod_lt _ (by decide)⟩) := by
  let next : Fin 5 := ⟨(lane.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
  let last : Fin 5 := ⟨(lane.val + 2) % 5, Nat.mod_lt _ (by decide)⟩
  have a (i : Fin 4) := (chi5_lane_limb_value cached false w holds lane i).1
  have b (i : Fin 4) := (chi5_lane_limb_value cached false w holds next i).1
  have c (i : Fin 4) := (chi5_lane_limb_value cached false w holds last i).1
  have neg (i : Fin 4) : 65535 ^^^ (chi5LaneLimb cached false w next i).val < 2 ^ 16 :=
    Nat.xor_lt_two_pow (by decide) (b i)
  have paired (i : Fin 4) :
      (65535 ^^^ (chi5LaneLimb cached false w next i).val) &&&
        (chi5LaneLimb cached false w last i).val < 2 ^ 16 :=
    lt_of_le_of_lt Nat.and_le_left (neg i)
  have conjunction := andn_of_four_limbs (b 0) (b 1) (b 2) (c 0) (c 1) (c 2)
    (a₃ := (chi5LaneLimb cached false w next 3).val)
    (b₃ := (chi5LaneLimb cached false w last 3).val)
  change not64 (chi5LaneValue cached false w next) &&& chi5LaneValue cached false w last = _ at conjunction
  rw [conjunction]
  unfold chi5LaneValue
  rw [chi5_lane_limb_operation cached w holds lane 0, chi5_lane_limb_operation cached w holds lane 1,
    chi5_lane_limb_operation cached w holds lane 2, chi5_lane_limb_operation cached w holds lane 3]
  have assembled := xor_of_four_chunks (width := 16) (a 0) (a 1) (a 2)
    (paired 0) (paired 1) (paired 2) (a₃ := (chi5LaneLimb cached false w lane 3).val)
    (b₃ := (65535 ^^^ (chi5LaneLimb cached false w next 3).val) &&&
      (chi5LaneLimb cached false w last 3).val)
  norm_num only [Nat.reducePow] at assembled
  simpa only [Nat.xor_comm 65535] using assembled.symm

end Airbender.Keccak.Split.Native.Proofs
