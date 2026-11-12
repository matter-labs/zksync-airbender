module
public import Proven.KeccakSplit.ColumnParity.IotaQueries

@[expose] public section

/- The delayed iota on lane 0 of a column-parity call: the byte queries apply the
   selected round constant (ported from PR #585's SplitParityIotaBytes and
   SplitParityIotaOperation). -/

namespace Airbender.Keccak.Split.ColumnParity.Proofs
open Airbender.Trace Airbender.Arithmetic Airbender.Keccak.Split.RowProofs
set_option warningAsError true

theorem iota_zero_parts : ∀ round : Fin 32,
    iotaByte (round.val + 64) = 0 ∧ iotaByte (round.val + 192) = 0 ∧
      Call.roundConstant round.val / 65536 ^ 2 % 65536 = 0 := by
  decide +kernel

theorem iota_constant_limbs : ∀ (round : Fin 32) (j : Fin 3),
    iotaByte (round.val + 32 * (2 * (iotaLimb j).val)) +
      256 * iotaByte (round.val + 32 * (2 * (iotaLimb j).val + 1)) =
        Call.roundConstant round.val / 65536 ^ (iotaLimb j).val % 65536 := by
  decide +kernel

theorem iota_constant_word : ∀ round : Fin 32,
    packFourChunks 16 (fun limb => Call.roundConstant round.val / 65536 ^ limb.val % 65536) =
      Call.roundConstant round.val := by
  decide +kernel

theorem control_value (w : Nat → ZMod babyBearModulus) (round : Fin 32)
    (selected : (row w 1)[3] = (round.val : ZMod babyBearModulus)) (j : Fin 4) :
    (row w ⟨2 + j.val, by omega⟩)[1].val = round.val + 32 * iotaPosition j := by
  have field : (row w ⟨2 + j.val, by omega⟩)[1] =
      ((round.val + 32 * iotaPosition j : Nat) : ZMod babyBearModulus) := by
    rw [query_control, selected]; push_cast; ring
  have small : round.val + 32 * iotaPosition j < babyBearModulus := by
    have := round.isLt
    have : iotaPosition j ≤ 7 := by unfold iotaPosition; split_ifs <;> omega
    exact lt_of_lt_of_le (by omega : _ < 300) (by decide)
  rw [field, ZMod.val_natCast_of_lt small]

theorem byte_operation {w : Nat → ZMod babyBearModulus} (h : Holds w) (round : Fin 32)
    (selected : (row w 1)[3] = (round.val : ZMod babyBearModulus)) (j : Fin 4) :
    (row w ⟨2 + j.val, by omega⟩)[0].val < 256 ∧ (row w ⟨2 + j.val, by omega⟩)[2].val < 256 ∧
      (row w ⟨2 + j.val, by omega⟩)[2].val =
        (row w ⟨2 + j.val, by omega⟩)[0].val ^^^ iotaByte (round.val + 32 * iotaPosition j) := by
  obtain ⟨a, -, c, d⟩ := iota_facts h j
  rw [control_value w round selected j] at d
  exact ⟨a, c, d⟩

theorem low_zero {w : Nat → ZMod babyBearModulus} (h : Holds w) (round : Fin 32)
    (selected : (row w 1)[3] = (round.val : ZMod babyBearModulus)) :
    (inputLow w 0).val < 256 ∧
      (outputByte w 0 false).val = (inputLow w 0).val ^^^ iotaByte round.val := by
  have facts := byte_operation h round selected 0
  have q := low_query w
  have p0 : iotaPosition 0 = 0 := by rfl
  simp only [Fin.val_zero, Nat.add_zero, p0, Nat.mul_zero] at facts
  rw [q.1, q.2] at facts
  exact ⟨facts.1, facts.2.2⟩

theorem high_bytes {w : Nat → ZMod babyBearModulus} (h : Holds w) (round : Fin 32)
    (selected : (row w 1)[3] = (round.val : ZMod babyBearModulus)) (j : Fin 3) :
    (inputHigh w j).val < 256 ∧
      (outputByte w (iotaLimb j) true).val =
        (inputHigh w j).val ^^^ iotaByte (round.val + 32 * (2 * (iotaLimb j).val + 1)) := by
  have facts := byte_operation h round selected ⟨j.val + 1, by omega⟩
  have same : (⟨2 + (j.val + 1), by omega⟩ : Fin 22) = ⟨3 + j.val, by omega⟩ := by
    apply Fin.ext; dsimp only; omega
  have position : iotaPosition ⟨j.val + 1, by omega⟩ = 2 * (iotaLimb j).val + 1 := by
    fin_cases j <;> rfl
  dsimp only at facts
  rw [same, high_query, position] at facts
  exact ⟨facts.1, facts.2.2⟩

theorem output_byte_value {w : Nat → ZMod babyBearModulus} (h : Holds w) (limb : Fin 4) (high : Bool) :
    (outputByte w limb high).val < 256 := by
  have low := nibble_bound h 0 ⟨4 * limb.val + if high then 2 else 0, by split <;> omega⟩
  have upper := nibble_bound h 0 ⟨4 * limb.val + (if high then 2 else 0) + 1, by split <;> omega⟩
  have value := value_of_bounded_pair (radix := 16) (capacity := 16) (by decide) low upper
    (show _ = outputByte w limb high from rfl)
  rw [value]
  omega

theorem low_bytes {w : Nat → ZMod babyBearModulus} (h : Holds w) (round : Fin 32)
    (selected : (row w 1)[3] = (round.val : ZMod babyBearModulus)) (j : Fin 3) :
    (inputLow w j).val < 256 ∧
      (outputByte w (iotaLimb j) false).val =
        (inputLow w j).val ^^^ iotaByte (round.val + 32 * (2 * (iotaLimb j).val)) := by
  fin_cases j
  · exact low_zero h round selected
  · change (inputLow w 1).val < 256 ∧
      (outputByte w 1 false).val = (inputLow w 1).val ^^^ iotaByte (round.val + 64)
    have equation : inputLow w 1 = outputByte w 1 false := unchanged_low h 0
    rw [equation, (iota_zero_parts round).1, Nat.xor_zero]
    exact ⟨output_byte_value h 1 false, rfl⟩
  · change (inputLow w 2).val < 256 ∧
      (outputByte w 3 false).val = (inputLow w 2).val ^^^ iotaByte (round.val + 192)
    have equation : inputLow w 2 = outputByte w 3 false := unchanged_low h 1
    rw [equation, (iota_zero_parts round).2.1, Nat.xor_zero]
    exact ⟨output_byte_value h 3 false, rfl⟩

theorem read_limb_value {w : Nat → ZMod babyBearModulus} (h : Holds w) (round : Fin 32)
    (selected : (row w 1)[3] = (round.val : ZMod babyBearModulus)) (j : Fin 3) :
    (limbOf w false 0 (iotaLimb j)).val < 65536 ∧
      (limbOf w false 0 (iotaLimb j)).val = (inputLow w j).val + 256 * (inputHigh w j).val := by
  have low := (low_bytes h round selected j).1
  have high := (high_bytes h round selected j).1
  have value := value_of_bounded_pair (radix := 256) (capacity := 256) (by decide) low high
    (read_packing w j).symm
  exact ⟨by rw [value]; omega, value⟩

theorem affected_limb_operation {w : Nat → ZMod babyBearModulus} (h : Holds w) (round : Fin 32)
    (selected : (row w 1)[3] = (round.val : ZMod babyBearModulus)) (j : Fin 3) :
    (limbOf w true 0 (iotaLimb j)).val = (limbOf w false 0 (iotaLimb j)).val ^^^
      (Call.roundConstant round.val / 65536 ^ (iotaLimb j).val % 65536) := by
  have low := low_bytes h round selected j
  have high := high_bytes h round selected j
  have written := value_of_bounded_pair (radix := 256) (capacity := 256) (by decide)
    (output_byte_value h (iotaLimb j) false) (output_byte_value h (iotaLimb j) true)
    (write_packing w (iotaLimb j)).symm
  rw [written, low.2, high.2]
  have joined := xor_of_chunks (width := 8) low.1
    (show iotaByte (round.val + 32 * (2 * (iotaLimb j).val)) < 2 ^ 8 from Nat.mod_lt _ (by decide))
    (a₁ := (inputHigh w j).val)
    (b₁ := iotaByte (round.val + 32 * (2 * (iotaLimb j).val + 1)))
  norm_num only [Nat.reducePow] at joined
  rw [← joined, ← (read_limb_value h round selected j).2, iota_constant_limbs]

theorem read_limb_bound {w : Nat → ZMod babyBearModulus} (h : Holds w) (round : Fin 32)
    (selected : (row w 1)[3] = (round.val : ZMod babyBearModulus)) (limb : Fin 4) :
    (limbOf w false 0 limb).val < 65536 := by
  fin_cases limb
  · exact (read_limb_value h round selected 0).1
  · exact (read_limb_value h round selected 1).1
  · change (limbOf w false 0 (2 : Fin 4)).val < 65536
    rw [unchanged_limb h]
    exact (write_limb_value h 0 2).1
  · exact (read_limb_value h round selected 2).1

theorem iota_limb_operation {w : Nat → ZMod babyBearModulus} (h : Holds w) (round : Fin 32)
    (selected : (row w 1)[3] = (round.val : ZMod babyBearModulus)) (limb : Fin 4) :
    (limbOf w true 0 limb).val = (limbOf w false 0 limb).val ^^^
      (Call.roundConstant round.val / 65536 ^ limb.val % 65536) := by
  fin_cases limb
  · exact affected_limb_operation h round selected 0
  · exact affected_limb_operation h round selected 1
  · change (limbOf w true 0 (2 : Fin 4)).val =
      (limbOf w false 0 (2 : Fin 4)).val ^^^ (Call.roundConstant round.val / 65536 ^ 2 % 65536)
    rw [← unchanged_limb h, (iota_zero_parts round).2.2, Nat.xor_zero]
  · exact affected_limb_operation h round selected 2

theorem iota_lane_operation {w : Nat → ZMod babyBearModulus} (h : Holds w) (round : Fin 32)
    (selected : (row w 1)[3] = (round.val : ZMod babyBearModulus)) :
    laneValue w true 0 = laneValue w false 0 ^^^ Call.roundConstant round.val := by
  let readValue (limb : Fin 4) := (limbOf w false 0 limb).val
  let constant (limb : Fin 4) := Call.roundConstant round.val / 65536 ^ limb.val % 65536
  have readBound (limb : Fin 4) : readValue limb < 2 ^ 16 := read_limb_bound h round selected limb
  have constantBound (limb : Fin 4) : constant limb < 2 ^ 16 := Nat.mod_lt _ (by decide)
  have outputs : (fun limb => (limbOf w true 0 limb).val) =
      (fun limb => readValue limb ^^^ constant limb) := by
    funext limb
    exact iota_limb_operation h round selected limb
  unfold laneValue
  rw [outputs, pack_four_xor _ _ readBound constantBound, iota_constant_word]

end Airbender.Keccak.Split.ColumnParity.Proofs
