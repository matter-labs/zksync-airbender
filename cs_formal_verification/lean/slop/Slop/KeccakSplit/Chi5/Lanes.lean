module
public import Slop.KeccakSplit.Chi5.Packing
public import Slop.Arithmetic.BitwiseAssembly

@[expose] public section

/- Chi on whole 64-bit lanes from the nibble queries (ported from PR #585's
   SplitChiLimbValues, SplitChiLimbOperation, SplitChiLaneOperation). -/

namespace Airbender.Keccak.Split.Chi5.Proofs
open Airbender.Trace Airbender.Arithmetic Airbender.Keccak.Split.RowProofs
set_option warningAsError true

theorem nibble_values {w : Nat → ZMod babyBearModulus} (h : Holds w)
    (lane : Fin 5) (digit : Fin 16) :
    (nibble w false lane digit).val < 16 ∧
    (nibble w true lane digit).val < 16 ∧
    (nibble w true lane digit).val = (nibble w false lane digit).val ^^^
      ((15 ^^^ (nibble w false ⟨(lane.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ digit).val) &&&
        (nibble w false ⟨(lane.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ digit).val) := by
  have values := nibble_facts h digit
  simpa only [nibble, Bool.false_eq_true, ↓reduceIte] using
    And.intro (values.1 lane) (values.2 lane)

theorem limb_value {w : Nat → ZMod babyBearModulus} (h : Holds w) (writing : Bool)
    (lane : Fin 5) (limb : Fin 4) :
    (limbOf w writing lane limb).val < 65536 ∧
    (limbOf w writing lane limb).val =
      (nibble w writing lane ⟨4 * limb.val, by omega⟩).val +
        16 * ((nibble w writing lane ⟨4 * limb.val + 1, by omega⟩).val +
          16 * ((nibble w writing lane ⟨4 * limb.val + 2, by omega⟩).val +
            16 * (nibble w writing lane ⟨4 * limb.val + 3, by omega⟩).val)) := by
  have bound (digit : Fin 16) : (nibble w writing lane digit).val < 16 := by
    have values := nibble_values h lane digit
    cases writing
    · exact values.1
    · exact values.2.1
  have h0 := bound ⟨4 * limb.val, by omega⟩
  have h1 := bound ⟨4 * limb.val + 1, by omega⟩
  have h2 := bound ⟨4 * limb.val + 2, by omega⟩
  have h3 := bound ⟨4 * limb.val + 3, by omega⟩
  have value := value_of_nibbles h0 h1 h2 h3 (packing w writing lane limb)
  exact ⟨by rw [value]; omega, value⟩

/-- Four low-to-high nibble values. -/
def packNibbles (digits : Fin 4 → Nat) : Nat :=
  digits 0 + 16 * (digits 1 + 16 * (digits 2 + 16 * digits 3))

/-- Chi commutes with the bounded four-nibble expansion. -/
theorem four_nibbles (a b c : Fin 4 → Nat)
    (ha : ∀ i, a i < 16) (hb : ∀ i, b i < 16) (hc : ∀ i, c i < 16) :
    packNibbles (fun i => a i ^^^ ((15 ^^^ b i) &&& c i)) =
      packNibbles a ^^^ ((65535 ^^^ packNibbles b) &&& packNibbles c) := by
  have complement := xor_of_four_chunks (width := 4)
    (a₀ := 15) (a₁ := 15) (a₂ := 15) (a₃ := 15)
    (by decide) (by decide) (by decide) (hb 0) (hb 1) (hb 2) (b₃ := b 3)
  change 65535 ^^^ packNibbles b = packNibbles (fun i => 15 ^^^ b i) at complement
  rw [complement]
  have negBound (i : Fin 4) : 15 ^^^ b i < 2 ^ 4 :=
    Nat.xor_lt_two_pow (by decide) (hb i)
  have conjunction := and_of_four_chunks (width := 4)
    (negBound 0) (negBound 1) (negBound 2) (hc 0) (hc 1) (hc 2)
    (a₃ := 15 ^^^ b 3) (b₃ := c 3)
  change packNibbles (fun i => 15 ^^^ b i) &&& packNibbles c =
    packNibbles (fun i => (15 ^^^ b i) &&& c i) at conjunction
  rw [conjunction]
  have pairBound (i : Fin 4) : (15 ^^^ b i) &&& c i < 2 ^ 4 :=
    lt_of_le_of_lt Nat.and_le_left (negBound i)
  exact (xor_of_four_chunks (width := 4) (ha 0) (ha 1) (ha 2)
    (pairBound 0) (pairBound 1) (pairBound 2) (a₃ := a 3)
    (b₃ := (15 ^^^ b 3) &&& c 3)).symm

/-- Every written limb is chi of the three cyclic read limbs. -/
theorem limb_operation {w : Nat → ZMod babyBearModulus} (h : Holds w) (lane : Fin 5) (limb : Fin 4) :
    (limbOf w true lane limb).val = (limbOf w false lane limb).val ^^^
      ((65535 ^^^ (limbOf w false ⟨(lane.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ limb).val) &&&
        (limbOf w false ⟨(lane.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ limb).val) := by
  let digit (i : Fin 4) : Fin 16 := ⟨4 * limb.val + i.val, by have := i.isLt; omega⟩
  let a (i : Fin 4) := (nibble w false lane (digit i)).val
  let b (i : Fin 4) := (nibble w false ⟨(lane.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ (digit i)).val
  let c (i : Fin 4) := (nibble w false ⟨(lane.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ (digit i)).val
  have input (column : Fin 5) := (limb_value h false column limb).2
  have output := (limb_value h true lane limb).2
  rw [output, input lane, input ⟨(lane.val + 1) % 5, Nat.mod_lt _ (by decide)⟩,
    input ⟨(lane.val + 2) % 5, Nat.mod_lt _ (by decide)⟩]
  have outputDigit (i : Fin 4) := (nibble_values h lane (digit i)).2.2
  change packNibbles (fun i => (nibble w true lane (digit i)).val) =
    packNibbles a ^^^ ((65535 ^^^ packNibbles b) &&& packNibbles c)
  have outputs : (fun i => (nibble w true lane (digit i)).val) =
      (fun i => a i ^^^ ((15 ^^^ b i) &&& c i)) := by
    funext i
    exact outputDigit i
  rw [outputs]
  exact four_nibbles a b c
    (fun i => (nibble_values h lane (digit i)).1)
    (fun i => (nibble_values h _ (digit i)).1)
    (fun i => (nibble_values h _ (digit i)).1)

/-- The four memory limbs of a lane as one 64-bit value. -/
def laneValue (w : Nat → ZMod babyBearModulus) (writing : Bool) (lane : Fin 5) : Nat :=
  (limbOf w writing lane 0).val + 65536 *
    ((limbOf w writing lane 1).val + 65536 *
      ((limbOf w writing lane 2).val + 65536 * (limbOf w writing lane 3).val))

theorem lane_bound {w : Nat → ZMod babyBearModulus} (h : Holds w) (writing : Bool) (lane : Fin 5) :
    laneValue w writing lane < 2 ^ 64 := by
  have h0 := (limb_value h writing lane 0).1
  have h1 := (limb_value h writing lane 1).1
  have h2 := (limb_value h writing lane 2).1
  have h3 := (limb_value h writing lane 3).1
  unfold laneValue
  norm_num only [Nat.reducePow]
  omega

/-- Chi on each complete lane. -/
theorem lane_operation {w : Nat → ZMod babyBearModulus} (h : Holds w) (lane : Fin 5) :
    laneValue w true lane = laneValue w false lane ^^^
      (not64 (laneValue w false ⟨(lane.val + 1) % 5, Nat.mod_lt _ (by decide)⟩) &&&
        laneValue w false ⟨(lane.val + 2) % 5, Nat.mod_lt _ (by decide)⟩) := by
  let next : Fin 5 := ⟨(lane.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
  let last : Fin 5 := ⟨(lane.val + 2) % 5, Nat.mod_lt _ (by decide)⟩
  have a (i : Fin 4) := (limb_value h false lane i).1
  have b (i : Fin 4) := (limb_value h false next i).1
  have c (i : Fin 4) := (limb_value h false last i).1
  have neg (i : Fin 4) : 65535 ^^^ (limbOf w false next i).val < 2 ^ 16 :=
    Nat.xor_lt_two_pow (by decide) (b i)
  have paired (i : Fin 4) :
      (65535 ^^^ (limbOf w false next i).val) &&& (limbOf w false last i).val < 2 ^ 16 :=
    lt_of_le_of_lt Nat.and_le_left (neg i)
  have conjunction := andn_of_four_limbs (b 0) (b 1) (b 2) (c 0) (c 1) (c 2)
    (a₃ := (limbOf w false next 3).val) (b₃ := (limbOf w false last 3).val)
  change not64 (laneValue w false next) &&& laneValue w false last = _ at conjunction
  rw [conjunction]
  unfold laneValue
  rw [limb_operation h lane 0, limb_operation h lane 1, limb_operation h lane 2,
    limb_operation h lane 3]
  have assembled := xor_of_four_chunks (width := 16) (a 0) (a 1) (a 2)
    (paired 0) (paired 1) (paired 2) (a₃ := (limbOf w false lane 3).val)
    (b₃ := (65535 ^^^ (limbOf w false next 3).val) &&& (limbOf w false last 3).val)
  norm_num only [Nat.reducePow] at assembled
  simpa only [Nat.xor_comm 65535] using assembled.symm

end Airbender.Keccak.Split.Chi5.Proofs
