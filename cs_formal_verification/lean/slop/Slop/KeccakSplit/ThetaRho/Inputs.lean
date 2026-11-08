module
public import Slop.KeccakSplit.ThetaRho.Bytes
public import Slop.Arithmetic.LaneRotation

@[expose] public section

/- Theta/rho input lanes: state and C[x-1] limbs from their query bytes, C[x+1]
   rotated by one through its carry columns, and D = C[x-1] ^ rot(C[x+1], 1)
   (ported from PR #585's SplitThetaInputPacking, SplitThetaNextRotation and
   SplitThetaDOperation). -/

namespace Airbender.Keccak.Split.ThetaRho.Proofs
open Airbender.Trace Airbender.Arithmetic Airbender.Keccak.Split.RowProofs
set_option warningAsError true

theorem state_limb_packing (w : Nat → ZMod babyBearModulus) (lane : Fin 5) (limb : Fin 4) :
    limbOf w false ⟨lane.val, by omega⟩ limb =
      stateByte w lane ⟨2 * limb.val, by omega⟩ + 256 * stateByte w lane ⟨2 * limb.val + 1, by omega⟩ := by
  apply byte_pack
  fin_cases lane <;> fin_cases limb <;>
    simp only [stateByte, limbOf, limbColumn, row_entry, query] <;> (op_index) <;>
    simp [Expression.eval, Verification.environment, readCol]

theorem previous_limb_packing (w : Nat → ZMod babyBearModulus) (limb : Fin 4) :
    limbOf w false 5 limb =
      previousByte w ⟨2 * limb.val, by omega⟩ + 256 * previousByte w ⟨2 * limb.val + 1, by omega⟩ := by
  apply byte_pack
  fin_cases limb <;>
    simp only [previousByte, limbOf, limbColumn, row_entry, query] <;> (op_index) <;>
    simp [Expression.eval, Verification.environment, readCol]

theorem state_limb_value {w : Nat → ZMod babyBearModulus} (h : Holds w) (lane : Fin 5) (limb : Fin 4) :
    (limbOf w false ⟨lane.val, by omega⟩ limb).val < 65536 ∧
      (limbOf w false ⟨lane.val, by omega⟩ limb).val =
        (stateByte w lane ⟨2 * limb.val, by omega⟩).val +
          256 * (stateByte w lane ⟨2 * limb.val + 1, by omega⟩).val := by
  have low := state_byte_bound h lane ⟨2 * limb.val, by omega⟩
  have high := state_byte_bound h lane ⟨2 * limb.val + 1, by omega⟩
  have value := value_of_bounded_pair (radix := 256) (capacity := 256) (by decide) low high
    (state_limb_packing w lane limb).symm
  exact ⟨by rw [value]; omega, value⟩

theorem previous_limb_value {w : Nat → ZMod babyBearModulus} (h : Holds w) (limb : Fin 4) :
    (limbOf w false 5 limb).val < 65536 ∧
      (limbOf w false 5 limb).val =
        (previousByte w ⟨2 * limb.val, by omega⟩).val +
          256 * (previousByte w ⟨2 * limb.val + 1, by omega⟩).val := by
  have low := (d_operand_bounds h ⟨2 * limb.val, by omega⟩).1
  have high := (d_operand_bounds h ⟨2 * limb.val + 1, by omega⟩).1
  have value := value_of_bounded_pair (radix := 256) (capacity := 256) (by decide) low high
    (previous_limb_packing w limb).symm
  exact ⟨by rw [value]; omega, value⟩

/-- The top-bit carry column of limb `limb` of C[x+1]. -/
def topOf (w : Nat → ZMod babyBearModulus) (limb : Fin 4) : ZMod babyBearModulus := w (68 + limb.val)

theorem top_bit {w : Nat → ZMod babyBearModulus} (h : Holds w) (limb : Fin 4) :
    topOf w limb = 0 ∨ topOf w limb = 1 := by
  have poly : topOf w limb * (topOf w limb - 1) = 0 := by
    fin_cases limb
    · have e := Verification.assertion_of_holds (core h) ⟨31, by decide⟩
      op_index at e
      simp only [Expression.eval, Verification.environment, Int.cast_negSucc] at e
      simp only [topOf]; linear_combination e
    · have e := Verification.assertion_of_holds (core h) ⟨32, by decide⟩
      op_index at e
      simp only [Expression.eval, Verification.environment, Int.cast_negSucc] at e
      simp only [topOf]; linear_combination e
    · have e := Verification.assertion_of_holds (core h) ⟨33, by decide⟩
      op_index at e
      simp only [Expression.eval, Verification.environment, Int.cast_negSucc] at e
      simp only [topOf]; linear_combination e
    · have e := Verification.assertion_of_holds (core h) ⟨34, by decide⟩
      op_index at e
      simp only [Expression.eval, Verification.environment, Int.cast_negSucc] at e
      simp only [topOf]; linear_combination e
  rcases mul_eq_zero.mp poly with zero | one
  · exact Or.inl zero
  · exact Or.inr (sub_eq_zero.mp one)

theorem top_bound {w : Nat → ZMod babyBearModulus} (h : Holds w) (limb : Fin 4) :
    (topOf w limb).val < 2 := by
  rcases top_bit h limb with zero | one
  · simp [zero]
  · rw [one]; decide

theorem rot_eq {L t t' r n : ZMod babyBearModulus}
    (hn : n = -15728640 * L - 256 * t' - 7864320 * t + 7864320 * r) :
    2 * L + t = r + 256 * n + 65536 * t' := by
  subst hn
  linear_combination (2 * L + t - r) * char

theorem next_rotation_equation (w : Nat → ZMod babyBearModulus) (limb : Fin 4) :
    2 * limbOf w false 6 limb + topOf w (rotationPrevious limb) =
      rotatedByte w ⟨2 * limb.val, by omega⟩ + 256 * rotatedByte w ⟨2 * limb.val + 1, by omega⟩ +
        65536 * topOf w limb := by
  apply rot_eq
  fin_cases limb <;>
    simp only [rotatedByte, limbOf, limbColumn, topOf, rotationPrevious, row_entry, query] <;>
    (op_index) <;> simp [Expression.eval, Verification.environment, readCol] <;> ring

/-- The two rotated bytes of limb `limb` of rot(C[x+1], 1). -/
noncomputable def rotatedLimbValue (w : Nat → ZMod babyBearModulus) (limb : Fin 4) : Nat :=
  (rotatedByte w ⟨2 * limb.val, by omega⟩).val + 256 * (rotatedByte w ⟨2 * limb.val + 1, by omega⟩).val

theorem rotated_limb_bound {w : Nat → ZMod babyBearModulus} (h : Holds w) (limb : Fin 4) :
    rotatedLimbValue w limb < 65536 := by
  have low := (d_operand_bounds h ⟨2 * limb.val, by omega⟩).2.1
  have high := (d_operand_bounds h ⟨2 * limb.val + 1, by omega⟩).2.1
  unfold rotatedLimbValue
  omega

theorem next_rotation_integer {w : Nat → ZMod babyBearModulus} (h : Holds w)
    (bounds : ∀ limb : Fin 4, (limbOf w false 6 limb).val < 65536) (limb : Fin 4) :
    2 * (limbOf w false 6 limb).val + (topOf w (rotationPrevious limb)).val =
      rotatedLimbValue w limb + 65536 * (topOf w limb).val := by
  have low := (d_operand_bounds h ⟨2 * limb.val, by omega⟩).2.1
  have high := (d_operand_bounds h ⟨2 * limb.val + 1, by omega⟩).2.1
  have carry := top_bound h (rotationPrevious limb)
  have top := top_bound h limb
  have input := bounds limb
  have leftBound : 2 * (limbOf w false 6 limb).val + (topOf w (rotationPrevious limb)).val <
      babyBearModulus := lt_of_lt_of_le (by omega : _ < 200000) (by decide)
  have rightBound : rotatedLimbValue w limb + 65536 * (topOf w limb).val < babyBearModulus := by
    unfold rotatedLimbValue
    exact lt_of_lt_of_le (by omega : _ < 200000) (by decide)
  have field :
      ((2 * (limbOf w false 6 limb).val + (topOf w (rotationPrevious limb)).val : Nat) :
        ZMod babyBearModulus) =
      ((rotatedLimbValue w limb + 65536 * (topOf w limb).val : Nat) : ZMod babyBearModulus) := by
    simpa only [rotatedLimbValue, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      ZMod.natCast_zmod_val] using next_rotation_equation w limb
  have equality := congrArg ZMod.val field
  simpa only [ZMod.val_natCast_of_lt leftBound, ZMod.val_natCast_of_lt rightBound] using equality

theorem top_value {w : Nat → ZMod babyBearModulus} (h : Holds w)
    (bounds : ∀ limb : Fin 4, (limbOf w false 6 limb).val < 65536) (limb : Fin 4) :
    (topOf w limb).val = (limbOf w false 6 limb).val / 32768 := by
  have equation := next_rotation_integer h bounds limb
  have carry := top_bound h (rotationPrevious limb)
  have top := top_bound h limb
  have rotated := rotated_limb_bound h limb
  have input := bounds limb
  omega

theorem rotated_limb_value {w : Nat → ZMod babyBearModulus} (h : Holds w)
    (bounds : ∀ limb : Fin 4, (limbOf w false 6 limb).val < 65536) (limb : Fin 4) :
    rotatedLimbValue w limb =
      (2 * (limbOf w false 6 limb).val) % 65536 + (limbOf w false 6 (rotationPrevious limb)).val / 32768 := by
  have equation := next_rotation_integer h bounds limb
  rw [top_value h bounds limb, top_value h bounds (rotationPrevious limb)] at equation
  have input := bounds limb
  omega

/-- C[x+1] as one lane, and the lane of its rotated query bytes. -/
noncomputable def nextLaneValue (w : Nat → ZMod babyBearModulus) : Nat :=
  packLane (Vector.ofFn fun limb : Fin 4 => (limbOf w false 6 limb).val)

noncomputable def rotatedLaneValue (w : Nat → ZMod babyBearModulus) : Nat :=
  packLane (Vector.ofFn fun limb : Fin 4 => rotatedLimbValue w limb)

theorem next_rotation {w : Nat → ZMod babyBearModulus} (h : Holds w)
    (bounds : ∀ limb : Fin 4, (limbOf w false 6 limb).val < 65536) :
    rotatedLaneValue w = rotLeft64 (nextLaneValue w) 1 := by
  let inputs : Vector Nat 4 := Vector.ofFn fun limb : Fin 4 => (limbOf w false 6 limb).val
  have small (limb : Fin 4) : inputs[limb] < 65536 := by
    simpa [inputs] using bounds limb
  have rotation := rotate_left_of_limbs small (1 : Fin 64)
  have equal : Vector.ofFn (rotatedLimbValue w) = (Vector.finRange 4).map (rotatedLaneLimb inputs 1) := by
    apply Vector.ext
    intro index bound
    have value := rotated_limb_value h bounds ⟨index, bound⟩
    interval_cases index
    all_goals simpa [inputs, rotatedLaneLimb, rotationSource, rotationPrevious, Nat.mul_comm] using value
  change packLane (Vector.ofFn (rotatedLimbValue w)) = rotLeft64 (packLane inputs) 1
  rw [equal]
  exact rotation.symm

/-- Limb `limb` of D, from its two query bytes. -/
noncomputable def dLimbValue (w : Nat → ZMod babyBearModulus) (limb : Fin 4) : Nat :=
  (dByte w ⟨2 * limb.val, by omega⟩).val + 256 * (dByte w ⟨2 * limb.val + 1, by omega⟩).val

theorem d_limb_operation {w : Nat → ZMod babyBearModulus} (h : Holds w) (limb : Fin 4) :
    dLimbValue w limb = (limbOf w false 5 limb).val ^^^ rotatedLimbValue w limb := by
  have previous := (previous_limb_value h limb).2
  have low := d_operand_bounds h ⟨2 * limb.val, by omega⟩
  have chunks := xor_of_chunks (width := 8) low.1 low.2.1
    (a₁ := (previousByte w ⟨2 * limb.val + 1, by omega⟩).val)
    (b₁ := (rotatedByte w ⟨2 * limb.val + 1, by omega⟩).val)
  norm_num only [Nat.reducePow] at chunks
  rw [previous]
  unfold rotatedLimbValue dLimbValue
  rw [d_byte_operation h ⟨2 * limb.val, by omega⟩, d_byte_operation h ⟨2 * limb.val + 1, by omega⟩]
  exact chunks.symm

noncomputable def dLaneValue (w : Nat → ZMod babyBearModulus) : Nat :=
  packLane (Vector.ofFn fun limb : Fin 4 => dLimbValue w limb)

noncomputable def previousLaneValue (w : Nat → ZMod babyBearModulus) : Nat :=
  packLane (Vector.ofFn fun limb : Fin 4 => (limbOf w false 5 limb).val)

theorem d_lane_operation {w : Nat → ZMod babyBearModulus} (h : Holds w) :
    dLaneValue w = previousLaneValue w ^^^ rotatedLaneValue w := by
  have a (limb : Fin 4) := (previous_limb_value h limb).1
  have b (limb : Fin 4) := rotated_limb_bound h limb
  have chunks := xor_of_four_chunks (width := 16) (a 0) (a 1) (a 2) (b 0) (b 1) (b 2)
    (a₃ := (limbOf w false 5 3).val) (b₃ := rotatedLimbValue w 3)
  norm_num only [Nat.reducePow] at chunks
  unfold dLaneValue previousLaneValue rotatedLaneValue packLane
  simp only [Vector.getElem_ofFn, d_limb_operation h]
  exact chunks.symm

/-- D = C[x-1] ^ rot(C[x+1], 1), given canonical C[x+1] reads. -/
theorem d_reference {w : Nat → ZMod babyBearModulus} (h : Holds w)
    (bounds : ∀ limb : Fin 4, (limbOf w false 6 limb).val < 65536) :
    dLaneValue w = previousLaneValue w ^^^ rotLeft64 (nextLaneValue w) 1 := by
  rw [d_lane_operation h, next_rotation h bounds]

end Airbender.Keccak.Split.ThetaRho.Proofs
