module
public import Slop.NonVacuous.KeccakSplitSpan.ThetaRho.Tables
public import Slop.NonVacuous.KeccakSplitSpan.ThetaRho.RotationA

@[expose] public section

/-! Facts the theta+rho lookups use: each lane's shift entry (the flags weighted by the column's rho mod 8) is the
    honest shift, the honest bytes and shifts are in range, and two tactics for honest entries. -/

namespace Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
open Arithmetic Keccak.Split Keccak.Split.SetupProofs

/-- A theta+rho entry whose evaluation is the honest value. -/
macro "theta_direct" : tactic => `(tactic| (
  simp only [Expression.eval, Verification.environment, honest_column, RowInput.control, flag, cByte, rByte,
    inByte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, ↓reduceIte, OfNat.ofNat_ne_zero, zero_ne_one,
    one_ne_zero]
  try push_cast
  try ring))

/-- A theta+rho XOR or fragment entry: the honest column is the table's value by definition. -/
macro "theta_result" : tactic => `(tactic| (
  simp only [Expression.eval, Verification.environment, honest_column]
  push_cast
  simp only [zero_add, one_mul]
  rfl))

theorem shift_0 (x : RowInput) : flag x 1 + 6 * flag x 2 + 4 * flag x 3 + 3 * flag x 4 = shift x 0 := by
  rcases column_cases x with c | c | c | c | c <;> simp only [flag, shift, rho, c, List.getD_cons_zero,
    List.getD_cons_succ, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte, zero_ne_one, mul_zero, mul_one, zero_add,
    add_zero]

theorem shift_1 (x : RowInput) :
    4 * flag x 0 + 4 * flag x 1 + 6 * flag x 2 + 7 * flag x 3 + 4 * flag x 4 = shift x 1 := by
  rcases column_cases x with c | c | c | c | c <;> simp only [flag, shift, rho, c, List.getD_cons_zero,
    List.getD_cons_succ, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte, OfNat.ofNat_ne_zero, zero_ne_one,
    one_ne_zero, mul_zero, mul_one, zero_add, add_zero]

theorem shift_2 (x : RowInput) : 3 * flag x 0 + 2 * flag x 1 + 3 * flag x 2 + flag x 3 + 7 * flag x 4 = shift x 2 := by
  rcases column_cases x with c | c | c | c | c <;> simp only [flag, shift, rho, c, List.getD_cons_zero,
    List.getD_cons_succ, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte, OfNat.ofNat_ne_zero, zero_ne_one,
    one_ne_zero, mul_zero, mul_one, zero_add, add_zero]

theorem shift_3 (x : RowInput) : flag x 0 + 5 * flag x 1 + 7 * flag x 2 + 5 * flag x 3 = shift x 3 := by
  rcases column_cases x with c | c | c | c | c <;> simp only [flag, shift, rho, c, List.getD_cons_zero,
    List.getD_cons_succ, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte, OfNat.ofNat_ne_zero, zero_ne_one,
    one_ne_zero, mul_zero, mul_one, zero_add, add_zero]

theorem shift_4 (x : RowInput) : 2 * flag x 0 + 2 * flag x 1 + 5 * flag x 2 + 6 * flag x 4 = shift x 4 := by
  rcases column_cases x with c | c | c | c | c <;> simp only [flag, shift, rho, c, List.getD_cons_zero,
    List.getD_cons_succ, Nat.reduceMod, Nat.reduceEqDiff, ↓reduceIte, OfNat.ofNat_ne_zero, zero_ne_one,
    one_ne_zero, mul_zero, mul_one, zero_add, add_zero]

theorem shift_lt (x : RowInput) (y : Nat) : shift x y < 8 := Nat.mod_lt _ (by decide)

theorem cByte_lt {x : RowInput} (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (j : Nat) :
    cByte x j < 256 := by
  have := valid.limb (l := 5) (by rw [kind]; decide) (j / 2)
  unfold cByte
  split <;> omega

theorem rByte_lt {x : RowInput} (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (j : Nat) :
    rByte x j < 256 := by
  have := valid.limb (l := 6) (by rw [kind]; decide) (j / 2)
  have := valid.limb (l := 6) (by rw [kind]; decide) ((j / 2 + 3) % 4)
  unfold rByte rotLimb top
  split <;> omega

theorem d_lt {x : RowInput} (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (j : Nat) : d x j < 256 :=
  Nat.xor_lt_two_pow (n := 8) (cByte_lt valid kind j) (rByte_lt valid kind j)

theorem inByte_lt {x : RowInput} (valid : x.Valid) (kind : kindAt x.call = .thetaRho) {y : Nat} (lane : y < 5)
    (j : Nat) : inByte x y j < 256 := by
  have := valid.limb (l := y) (by rw [kind]; change y < 7; omega) (j / 2)
  unfold inByte
  split <;> omega

/-- A written byte: fragment 0 of one byte (a multiple of `2^s`) plus fragment 1 of another (below `2^s`). -/
theorem outByte_lt {x : RowInput} (valid : x.Valid) (kind : kindAt x.call = .thetaRho) {y : Nat} (lane : y < 5)
    (n : Nat) : outByte x y n < 256 := by
  have bound (j : Nat) : inByte x y j ^^^ d x j < 256 :=
    Nat.xor_lt_two_pow (n := 8) (inByte_lt valid kind lane j) (d_lt valid kind j)
  have a := bound ((n + 8 - rho (x.call % 5) y / 8) % 8)
  have b := bound ((n + 7 - rho (x.call % 5) y / 8) % 8)
  unfold outByte frag0 frag1 shift
  generalize inByte x y ((n + 8 - rho (x.call % 5) y / 8) % 8) ^^^ d x ((n + 8 - rho (x.call % 5) y / 8) % 8) = A
    at a ⊢
  generalize inByte x y ((n + 7 - rho (x.call % 5) y / 8) % 8) ^^^ d x ((n + 7 - rho (x.call % 5) y / 8) % 8) = B
    at b ⊢
  have small : rho (x.call % 5) y % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize rho (x.call % 5) y % 8 = s at small ⊢
  interval_cases s <;> simp only [Nat.reducePow, Nat.reduceSub, ↓reduceIte, Nat.reduceEqDiff] <;> omega

theorem out_lt {x : RowInput} (valid : x.Valid) (kind : kindAt x.call = .thetaRho) {y : Nat} (lane : y < 5)
    (m : Nat) : out x y m < 65536 := by
  have low := outByte_lt valid kind lane (2 * m)
  have high := outByte_lt valid kind lane (2 * m + 1)
  unfold out
  omega

end Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
