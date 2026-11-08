module
public import Slop.KeccakSplit.ColumnParity.Lanes

@[expose] public section

/- The iota byte queries and equations of the column-parity worker, evaluated to their
   witness columns (ported from PR #585's SplitParityIotaPacking and
   SplitParityIotaConstraints). -/

namespace Airbender.Keccak.Split.ColumnParity.Proofs
open Airbender.Trace Airbender.Arithmetic Airbender.Keccak.Split.RowProofs
set_option warningAsError true

/-- The three input limbs split into bytes: limbs 0, 1 and 3. -/
def iotaLimb (j : Fin 3) : Fin 4 := ⟨if j.val < 2 then j.val else 3, by split <;> omega⟩

/-- Byte positions of the four iota byte queries. -/
def iotaPosition (j : Fin 4) : Nat :=
  if j.val = 0 then 0 else if j.val = 1 then 1 else if j.val = 2 then 3 else 7

/-- The low input byte of limb `iotaLimb j`. -/
def inputLow (w : Nat → ZMod babyBearModulus) (j : Fin 3) : ZMod babyBearModulus := w (48 + j.val)

/-- The high input byte of limb `iotaLimb j`, in its iota query. -/
noncomputable def inputHigh (w : Nat → ZMod babyBearModulus) (j : Fin 3) : ZMod babyBearModulus :=
  (row w ⟨3 + j.val, by omega⟩)[0]

/-- Byte `high` of written limb `limb` of lane 0, from its XOR nibbles. -/
noncomputable def outputByte (w : Nat → ZMod babyBearModulus) (limb : Fin 4) (high : Bool) :
    ZMod babyBearModulus :=
  nibble w 0 ⟨4 * limb.val + if high then 2 else 0, by split <;> omega⟩ +
    16 * nibble w 0 ⟨4 * limb.val + (if high then 2 else 0) + 1, by split <;> omega⟩

theorem read_packing (w : Nat → ZMod babyBearModulus) (j : Fin 3) :
    limbOf w false 0 (iotaLimb j) = inputLow w j + 256 * inputHigh w j := by
  apply byte_pack
  fin_cases j <;>
    simp only [inputHigh, limbOf, limbColumn, iotaLimb, inputLow, row_entry, query] <;> (op_index) <;>
    simp [Expression.eval, Verification.environment, readCol]

theorem write_packing (w : Nat → ZMod babyBearModulus) (limb : Fin 4) :
    limbOf w true 0 limb = outputByte w limb false + 256 * outputByte w limb true := by
  rw [packing]
  simp only [outputByte, Bool.false_eq_true, ite_true, ite_false, Nat.add_zero]
  ring

theorem low_query (w : Nat → ZMod babyBearModulus) :
    (row w ⟨2, by decide⟩)[0] = inputLow w 0 ∧ (row w ⟨2, by decide⟩)[2] = outputByte w 0 false := by
  constructor
  · simp only [inputLow, row_entry, query]; (op_index)
    simp [Expression.eval, Verification.environment]
  · simp only [outputByte, nibble, row_entry, query, Bool.false_eq_true, ↓reduceIte]; (op_index)
    simp [Expression.eval, Verification.environment]

theorem high_query0 (w : Nat → ZMod babyBearModulus) :
    (row w ⟨3, by decide⟩)[2] = outputByte w ⟨0, by decide⟩ true := by
  simp only [outputByte, nibble, row_entry, query, ↓reduceIte]; (op_index)
  simp [Expression.eval, Verification.environment]
  linear_combination (-(w 53)) * char

theorem high_query1 (w : Nat → ZMod babyBearModulus) :
    (row w ⟨4, by decide⟩)[2] = outputByte w ⟨1, by decide⟩ true := by
  simp only [outputByte, nibble, row_entry, query, ↓reduceIte]; (op_index)
  simp [Expression.eval, Verification.environment]
  linear_combination (-(w 56)) * char

theorem high_query2 (w : Nat → ZMod babyBearModulus) :
    (row w ⟨5, by decide⟩)[2] = outputByte w ⟨3, by decide⟩ true := by
  simp only [outputByte, nibble, row_entry, query, ↓reduceIte]; (op_index)
  simp [Expression.eval, Verification.environment]
  linear_combination (-(w 62)) * char

theorem high_query (w : Nat → ZMod babyBearModulus) (j : Fin 3) :
    (row w ⟨3 + j.val, by omega⟩)[2] = outputByte w (iotaLimb j) true := by
  fin_cases j
  · exact high_query0 w
  · exact high_query1 w
  · exact high_query2 w

theorem query_control (w : Nat → ZMod babyBearModulus) (j : Fin 4) :
    (row w ⟨2 + j.val, by omega⟩)[1] = (row w 1)[3] + 32 * (iotaPosition j : ZMod babyBearModulus) := by
  fin_cases j <;>
    simp only [iotaPosition, row_entry, query, Fin.val_one] <;> (op_index) <;>
    simp [Expression.eval, Verification.environment] <;> ring

theorem unchanged_low0 {w : Nat → ZMod babyBearModulus} (h : Holds w) :
    inputLow w ⟨1, by decide⟩ = outputByte w ⟨1, by decide⟩ false := by
  have e := Verification.assertion_of_holds (core h) ⟨3, by decide⟩
  op_index at e
  simp only [inputLow, outputByte, nibble, row_entry, query, Bool.false_eq_true, ↓reduceIte]
  (op_index)
  simp [Expression.eval, Verification.environment] at e ⊢
  linear_combination e

theorem unchanged_low1 {w : Nat → ZMod babyBearModulus} (h : Holds w) :
    inputLow w ⟨2, by decide⟩ = outputByte w ⟨3, by decide⟩ false := by
  have e := Verification.assertion_of_holds (core h) ⟨4, by decide⟩
  op_index at e
  simp only [inputLow, outputByte, nibble, row_entry, query, Bool.false_eq_true, ↓reduceIte]
  (op_index)
  simp [Expression.eval, Verification.environment] at e ⊢
  linear_combination e

theorem unchanged_low {w : Nat → ZMod babyBearModulus} (h : Holds w) (j : Fin 2) :
    inputLow w ⟨j.val + 1, by omega⟩ = outputByte w (iotaLimb ⟨j.val + 1, by omega⟩) false := by
  fin_cases j
  · exact unchanged_low0 h
  · exact unchanged_low1 h

theorem unchanged_limb {w : Nat → ZMod babyBearModulus} (h : Holds w) :
    limbOf w false 0 2 = limbOf w true 0 2 := by
  have e := Verification.assertion_of_holds (core h) ⟨5, by decide⟩
  op_index at e
  simp only [limbOf, limbColumn]
  simp [Expression.eval, Verification.environment, readCol, writeCol] at e ⊢
  linear_combination e

end Airbender.Keccak.Split.ColumnParity.Proofs
