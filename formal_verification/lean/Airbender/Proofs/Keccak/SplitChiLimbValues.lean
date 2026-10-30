import Airbender.Proofs.Keccak.SplitChiPacking
import Airbender.Proofs.Arithmetic.BitwiseAssembly

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxHeartbeats 1600000
variable [Fact babyBearModulus.Prime]

/-- Actual native queries bound each input and output nibble and enforce chi. -/
theorem chi5_nibble_values (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then Chi5Cached.clockConstraints chi5FixedTable else Chi5.clockConstraints chi5FixedTable))
    (lane : Fin 5) (digit : Fin 16) :
    (chi5Nibble cached false w lane digit).val < 16 ∧
    (chi5Nibble cached true w lane digit).val < 16 ∧
    (chi5Nibble cached true w lane digit).val = (chi5Nibble cached false w lane digit).val ^^^
      ((15 ^^^ (chi5Nibble cached false w ⟨(lane.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ digit).val) &&&
        (chi5Nibble cached false w ⟨(lane.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ digit).val) := by
  have values := chi5_native_arithmetic_queries cached w holds digit
  simpa only [chi5Nibble, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, Vector.getElem_map] using
    And.intro (values.1 lane) (values.2 lane)

/-- Four bounded field nibbles recover the canonical sixteen-bit value. -/
theorem chi5_value_of_nibbles {x a b c d : ZMod babyBearModulus}
    (ha : a.val < 16) (hb : b.val < 16) (hc : c.val < 16) (hd : d.val < 16)
    (equation : x = a + 16 * b + 256 * c + 4096 * d) :
    x.val = a.val + 16 * (b.val + 16 * (c.val + 16 * d.val)) := by
  have small : a.val + 16 * (b.val + 16 * (c.val + 16 * d.val)) < babyBearModulus := by
    exact lt_of_lt_of_le (by omega : _ < 65536) (by decide)
  have cast : ((a.val + 16 * (b.val + 16 * (c.val + 16 * d.val)) : Nat) :
      ZMod babyBearModulus) = x := by
    rw [equation]
    push_cast
    simp only [ZMod.natCast_zmod_val]
    ring
  rw [← cast]
  exact ZMod.val_natCast_of_lt small

/-- Each actual read or write limb has its canonical bounded nibble expansion. -/
theorem chi5_lane_limb_value (cached writing : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then Chi5Cached.clockConstraints chi5FixedTable else Chi5.clockConstraints chi5FixedTable))
    (lane : Fin 5) (limb : Fin 4) :
    (chi5LaneLimb cached writing w lane limb).val < 65536 ∧
    (chi5LaneLimb cached writing w lane limb).val =
      (chi5Nibble cached writing w lane ⟨4 * limb.val, by omega⟩).val +
        16 * ((chi5Nibble cached writing w lane ⟨4 * limb.val + 1, by omega⟩).val +
          16 * ((chi5Nibble cached writing w lane ⟨4 * limb.val + 2, by omega⟩).val +
            16 * (chi5Nibble cached writing w lane ⟨4 * limb.val + 3, by omega⟩).val)) := by
  have bound (digit : Fin 16) : (chi5Nibble cached writing w lane digit).val < 16 := by
    have values := chi5_nibble_values cached w holds lane digit
    cases writing
    · exact values.1
    · exact values.2.1
  have h0 := bound ⟨4 * limb.val, by omega⟩
  have h1 := bound ⟨4 * limb.val + 1, by omega⟩
  have h2 := bound ⟨4 * limb.val + 2, by omega⟩
  have h3 := bound ⟨4 * limb.val + 3, by omega⟩
  have value := chi5_value_of_nibbles h0 h1 h2 h3 (chi5_lane_packing cached writing w lane limb)
  exact ⟨by rw [value]; omega, value⟩

end Airbender.Keccak.Split.Native.Proofs
