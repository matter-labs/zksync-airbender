import Airbender.Proofs.Keccak.SplitChiLimbValues

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxHeartbeats 1600000

/-- Four low-to-high nibble values. -/
def chi5PackNibbles (digits : Fin 4 → Nat) : Nat :=
  digits 0 + 16 * (digits 1 + 16 * (digits 2 + 16 * digits 3))

/-- Chi commutes with the bounded four-nibble expansion. -/
theorem chi5_four_nibbles (a b c : Fin 4 → Nat)
    (ha : ∀ i, a i < 16) (hb : ∀ i, b i < 16) (hc : ∀ i, c i < 16) :
    chi5PackNibbles (fun i => a i ^^^ ((15 ^^^ b i) &&& c i)) =
      chi5PackNibbles a ^^^ ((65535 ^^^ chi5PackNibbles b) &&& chi5PackNibbles c) := by
  have complement := xor_of_four_chunks (width := 4)
    (a₀ := 15) (a₁ := 15) (a₂ := 15) (a₃ := 15)
    (by decide) (by decide) (by decide) (hb 0) (hb 1) (hb 2) (b₃ := b 3)
  change 65535 ^^^ chi5PackNibbles b = chi5PackNibbles (fun i => 15 ^^^ b i) at complement
  rw [complement]
  have negBound (i : Fin 4) : 15 ^^^ b i < 2 ^ 4 :=
    Nat.xor_lt_two_pow (by decide) (hb i)
  have conjunction := and_of_four_chunks (width := 4)
    (negBound 0) (negBound 1) (negBound 2) (hc 0) (hc 1) (hc 2)
    (a₃ := 15 ^^^ b 3) (b₃ := c 3)
  change chi5PackNibbles (fun i => 15 ^^^ b i) &&& chi5PackNibbles c =
    chi5PackNibbles (fun i => (15 ^^^ b i) &&& c i) at conjunction
  rw [conjunction]
  have pairBound (i : Fin 4) : (15 ^^^ b i) &&& c i < 2 ^ 4 :=
    lt_of_le_of_lt Nat.and_le_left (negBound i)
  exact (xor_of_four_chunks (width := 4) (ha 0) (ha 1) (ha 2)
    (pairBound 0) (pairBound 1) (pairBound 2) (a₃ := a 3)
    (b₃ := (15 ^^^ b 3) &&& c 3)).symm

variable [Fact babyBearModulus.Prime]

/-- Every actual chi5 write limb equals chi of the three cyclic read limbs. -/
theorem chi5_lane_limb_operation (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then Chi5Cached.clockConstraints chi5FixedTable else Chi5.clockConstraints chi5FixedTable))
    (lane : Fin 5) (limb : Fin 4) :
    (chi5LaneLimb cached true w lane limb).val = (chi5LaneLimb cached false w lane limb).val ^^^
      ((65535 ^^^ (chi5LaneLimb cached false w ⟨(lane.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ limb).val) &&&
        (chi5LaneLimb cached false w ⟨(lane.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ limb).val) := by
  let digit (i : Fin 4) : Fin 16 := ⟨4 * limb.val + i.val, by have := i.isLt; omega⟩
  let a (i : Fin 4) := (chi5Nibble cached false w lane (digit i)).val
  let b (i : Fin 4) := (chi5Nibble cached false w ⟨(lane.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ (digit i)).val
  let c (i : Fin 4) := (chi5Nibble cached false w ⟨(lane.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ (digit i)).val
  have input (column : Fin 5) := (chi5_lane_limb_value cached false w holds column limb).2
  have output := (chi5_lane_limb_value cached true w holds lane limb).2
  rw [output, input lane, input ⟨(lane.val + 1) % 5, Nat.mod_lt _ (by decide)⟩,
    input ⟨(lane.val + 2) % 5, Nat.mod_lt _ (by decide)⟩]
  have outputDigit (i : Fin 4) := (chi5_nibble_values cached w holds lane (digit i)).2.2
  change chi5PackNibbles (fun i => (chi5Nibble cached true w lane (digit i)).val) =
    chi5PackNibbles a ^^^ ((65535 ^^^ chi5PackNibbles b) &&& chi5PackNibbles c)
  have outputs : (fun i => (chi5Nibble cached true w lane (digit i)).val) =
      (fun i => a i ^^^ ((15 ^^^ b i) &&& c i)) := by
    funext i
    exact outputDigit i
  rw [outputs]
  exact chi5_four_nibbles a b c
    (fun i => (chi5_nibble_values cached w holds lane (digit i)).1)
    (fun i => (chi5_nibble_values cached w holds _ (digit i)).1)
    (fun i => (chi5_nibble_values cached w holds _ (digit i)).1)

end Airbender.Keccak.Split.Native.Proofs
