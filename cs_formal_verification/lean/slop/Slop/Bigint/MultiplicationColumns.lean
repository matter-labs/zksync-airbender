module
public import Slop.Bigint.MultiplicationRanges
public import Slop.Bigint.OpIndex
public import Slop.Arithmetic.Convolution
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

namespace Airbender.Bigint.Multiplication.Proofs
open Arithmetic
open scoped BigOperators
set_option warningAsError true

def incoming (w : Nat → ZMod p) (i : Fin 32) : ZMod p :=
  if first : i.val = 0 then 0 else carry w ⟨i.val - 1, by have := i.isLt; omega⟩

def outgoing (w : Nat → ZMod p) (i : Fin 32) : ZMod p :=
  if last : i.val < 31 then carry w ⟨i.val, last⟩ else 0

/-! The 32 imported column equations (constraints `19 + i`), as data. Column `i` adds, for every
left limb `j` with `k = i - j`, the byte products `l r + l (R - r) + (L - l) r` of limbs `j` and `k`
(`L`, `R` the limbs, `l`, `r` their low bytes) and, scaled by `2^-16`, the high-byte product
`(L - l) (R - r)` of limbs `j` and `k - 1`; it starts from the incoming carry and subtracts the
intermediate column. `column_shape` checks the imported constraints against the template, one closed
fact per index; `column_eval` evaluates the template once, for every column. -/
namespace Column

abbrev constant {p : Nat} (c : Int) : Expression (ZMod p) := Expression.const (c : ZMod p)

abbrev cell {p : Nat} (i : Nat) : Expression (ZMod p) := Expression.var ⟨i⟩

/-- `1 * a * b`. -/
abbrev product {p : Nat} (a b : Expression (ZMod p)) : Expression (ZMod p) :=
  ((constant (Int.ofNat 1)).mul a).mul b

/-- `w a - w b` as `0 + a + 1 * (-1) * b`. -/
abbrev diff {p : Nat} (a b : Nat) : Expression (ZMod p) :=
  ((constant (Int.ofNat 0)).add (cell a)).add (product (constant (Int.negSucc 0)) (cell b))

/-- Column of left limb `j` (`Variables.leftLimbs`). -/
def leftColumn (j : Nat) : Nat := 5 + 4 * (j / 2) + j % 2

/-- The cross terms of limbs `j` and `k`, before the high-byte term. -/
def lowFirst {p : Nat} (j k : Nat) (acc : Expression (ZMod p)) : Expression (ZMod p) :=
  if k < 16 then
    (acc.add (product (cell (99 + j)) (cell (115 + k)))).add
      (product (cell (99 + j)) (diff (39 + k) (115 + k)))
  else acc

/-- The high-byte product of limbs `j` and `k - 1`. -/
def highTerm {p : Nat} (j k : Nat) (acc : Expression (ZMod p)) : Expression (ZMod p) :=
  if 1 ≤ k ∧ k ≤ 16 then
    acc.add ((product (constant (Int.negSucc 30719)) (diff (leftColumn j) (99 + j))).mul
      (diff (39 + (k - 1)) (115 + (k - 1))))
  else acc

/-- The last cross term of limbs `j` and `k`. -/
def lowLast {p : Nat} (j k : Nat) (acc : Expression (ZMod p)) : Expression (ZMod p) :=
  if k < 16 then acc.add (product (diff (leftColumn j) (99 + j)) (cell (115 + k))) else acc

/-- The terms of left limb `j` in column `i`. -/
def step {p : Nat} (i j : Nat) (acc : Expression (ZMod p)) : Expression (ZMod p) :=
  if j ≤ i then lowLast j (i - j) (highTerm j (i - j) (lowFirst j (i - j) acc)) else acc

/-- The incoming carry of column `i`. -/
def start {p : Nat} (i : Nat) : Expression (ZMod p) :=
  if i = 0 then constant (Int.ofNat 0)
  else (constant (Int.ofNat 0)).add
    (product (constant (Int.negSucc 30719)) (diff (163 + (i - 1)) (131 + (i - 1))))

/-- The terms of the first `n` left limbs of column `i`. -/
def sum {p : Nat} (i : Nat) : Nat → Expression (ZMod p)
  | 0 => start i
  | n + 1 => step i n (sum i n)

/-- The intermediate column of column `i`; the last one is the product limb itself. -/
def output (i : Nat) : Nat := if i < 31 then 163 + i else 162

/-- Constraint `19 + i`. -/
def expr {p : Nat} (i : Nat) : Expression (ZMod p) :=
  (sum i 16).add (product (constant (Int.negSucc 0)) (cell (output i)))

end Column

theorem column_shape {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 3)) (i : Fin 32) :
    (FlatOperation.constraints (importedConstraints setup)).get
      ⟨19 + i.val, by rw [constraint_count]; omega⟩ = Column.expr i.val := by
  fin_cases i <;> op_index <;> rfl

section Evaluation

variable {p : Nat} [Fact p.Prime] (w : Nat → ZMod p)

/-- The value of the terms of limbs `j` and `i - j`. -/
def termAt (i j : Nat) : ZMod p :=
  if j ≤ i then
    (if i - j < 16 then
      w (99 + j) * w (115 + (i - j)) + w (99 + j) * (w (39 + (i - j)) - w (115 + (i - j))) +
        (w (Column.leftColumn j) - w (99 + j)) * w (115 + (i - j))
    else 0) +
    (if 1 ≤ i - j ∧ i - j ≤ 16 then
      (-30720 : ZMod p) * (w (Column.leftColumn j) - w (99 + j)) *
        (w (39 + (i - j - 1)) - w (115 + (i - j - 1)))
    else 0)
  else 0

private theorem step_eval (i j : Nat) (acc : Expression (ZMod p)) :
    (Column.step i j acc).eval (Verification.environment w) =
      acc.eval (Verification.environment w) + termAt w i j := by
  unfold Column.step termAt Column.lowLast Column.highTerm Column.lowFirst
  split_ifs <;> simp only [Expression.eval, Verification.environment] <;> push_cast <;> ring

private theorem sum_eval (i n : Nat) :
    (Column.sum i n : Expression (ZMod p)).eval (Verification.environment w) =
      (Column.start i).eval (Verification.environment w) +
        ∑ j ∈ Finset.range n, termAt w i j := by
  induction n with
  | zero => simp [Column.sum]
  | succ n ih => rw [Column.sum, step_eval, ih, Finset.sum_range_succ, add_assoc]

/-- Every imported column equation, evaluated once for all columns. -/
theorem column_eval (i : Nat) :
    (Column.expr i : Expression (ZMod p)).eval (Verification.environment w) =
      (if i = 0 then 0 else (-30720 : ZMod p) * (w (163 + (i - 1)) - w (131 + (i - 1)))) +
        ∑ j ∈ Finset.range 16, termAt w i j - w (Column.output i) := by
  rw [Column.expr, Expression.eval, sum_eval]
  unfold Column.start
  split_ifs <;> simp only [Expression.eval, Verification.environment] <;> push_cast <;> ring

end Evaluation

/-- One left limb's terms of column `i` are its byte products in the column, as naturals. -/
private theorem term_value {w : Nat → ZMod babyBearModulus} {left right : Fin 16 → Nat}
    (sources : ∀ i, w Variables.leftLimbs[i] = (left i : ZMod babyBearModulus) ∧
      w Variables.rightLimbs[i] = (right i : ZMod babyBearModulus))
    (bytes : ∀ i : Fin 16,
      w (99 + i.val) = ((left i % 256 : Nat) : ZMod babyBearModulus) ∧
      w (115 + i.val) = ((right i % 256 : Nat) : ZMod babyBearModulus))
    (i : Nat) (j : Fin 16) :
    termAt w i j.val = ((∑ k : Fin 16, (if j.val + k.val + 0 = i then
        byteCross (left j) (right k) else 0) +
      ∑ k : Fin 16, (if j.val + k.val + 1 = i then
        byteHigh (left j) (right k) else 0) : Nat) : ZMod babyBearModulus) := by
  have leftLimb : w (Column.leftColumn j.val) =
      ((left j % 256 : Nat) : ZMod babyBearModulus) +
        256 * ((left j / 256 : Nat) : ZMod babyBearModulus) := by
    have source := (sources j).1
    simp only [Variables.leftLimbs, Fin.getElem_fin, Vector.getElem_ofFn] at source
    rw [Column.leftColumn, source]
    have split := congrArg (fun n : Nat => (n : ZMod babyBearModulus)) (Nat.mod_add_div (left j) 256)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using split.symm
  have rightLimb (k : Fin 16) : w (39 + k.val) =
      ((right k % 256 : Nat) : ZMod babyBearModulus) +
        256 * ((right k / 256 : Nat) : ZMod babyBearModulus) := by
    have source := (sources k).2
    simp only [Variables.rightLimbs, Fin.getElem_fin, Vector.getElem_ofFn] at source
    rw [source]
    have split := congrArg (fun n : Nat => (n : ZMod babyBearModulus)) (Nat.mod_add_div (right k) 256)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using split.symm
  have scale : (-30720 : ZMod babyBearModulus) * 65536 = 1 := by decide
  have cross (k : Nat) (hk : k < 16) :
      w (99 + j.val) * w (115 + k) + w (99 + j.val) * (w (39 + k) - w (115 + k)) +
        (w (Column.leftColumn j.val) - w (99 + j.val)) * w (115 + k) =
      (byteCross (left j) (right ⟨k, hk⟩) : ZMod babyBearModulus) := by
    rw [leftLimb, rightLimb ⟨k, hk⟩, (bytes j).1, (bytes ⟨k, hk⟩).2, byteCross]
    push_cast
    ring
  have high (k : Nat) (hk : k < 16) :
      (-30720 : ZMod babyBearModulus) * (w (Column.leftColumn j.val) - w (99 + j.val)) *
        (w (39 + k) - w (115 + k)) =
      (byteHigh (left j) (right ⟨k, hk⟩) : ZMod babyBearModulus) := by
    rw [leftLimb, rightLimb ⟨k, hk⟩, (bytes j).1, (bytes ⟨k, hk⟩).2, byteHigh]
    push_cast
    linear_combination ((left j / 256 : Nat) : ZMod babyBearModulus) *
      ((right ⟨k, hk⟩ / 256 : Nat) : ZMod babyBearModulus) * scale
  have low (f : Fin 16 → Nat) :
      (∑ k : Fin 16, (if j.val + k.val + 0 = i then f k else 0)) =
        if h : j.val ≤ i ∧ i - j.val < 16 then f ⟨i - j.val, h.2⟩ else 0 := by
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨i - j.val, h.2⟩]
      · simp only [show j.val + (i - j.val) + 0 = i by omega, ↓reduceIte]
      · intro k _ other
        have : j.val + k.val + 0 ≠ i := fun same => other (Fin.ext (by simp only; omega))
        simp only [this, ↓reduceIte]
      · simp
    · apply Finset.sum_eq_zero
      intro k _
      have : j.val + k.val + 0 ≠ i := by have := k.isLt; omega
      simp only [this, ↓reduceIte]
  have shifted (f : Fin 16 → Nat) :
      (∑ k : Fin 16, (if j.val + k.val + 1 = i then f k else 0)) =
        if h : j.val ≤ i ∧ 1 ≤ i - j.val ∧ i - j.val ≤ 16 then
          f ⟨i - j.val - 1, by omega⟩ else 0 := by
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨i - j.val - 1, by omega⟩]
      · simp only [show j.val + (i - j.val - 1) + 1 = i by omega, ↓reduceIte]
      · intro k _ other
        have : j.val + k.val + 1 ≠ i := fun same => other (Fin.ext (by simp only; omega))
        simp only [this, ↓reduceIte]
      · simp
    · apply Finset.sum_eq_zero
      intro k _
      have : j.val + k.val + 1 ≠ i := by have := k.isLt; omega
      simp only [this, ↓reduceIte]
  rw [low (fun k => byteCross (left j) (right k)), shifted (fun k => byteHigh (left j) (right k))]
  unfold termAt
  by_cases below : j.val ≤ i
  · rw [ite_eq_left below]
    by_cases lowIn : i - j.val < 16
    · rw [ite_eq_left lowIn, dite_eq_left ⟨below, lowIn⟩, Nat.cast_add, ← cross _ lowIn]
      by_cases highIn : 1 ≤ i - j.val
      · rw [ite_eq_left ⟨highIn, by omega⟩, dite_eq_left ⟨below, highIn, by omega⟩, ← high _ (by omega)]
      · rw [ite_eq_right (by omega), dite_eq_right (by omega), Nat.cast_zero]
    · rw [ite_eq_right lowIn, dite_eq_right (by omega), zero_add, zero_add]
      by_cases highIn : i - j.val ≤ 16
      · rw [ite_eq_left ⟨by omega, highIn⟩, dite_eq_left ⟨below, by omega, highIn⟩, ← high _ (by omega)]
      · rw [ite_eq_right (by omega), dite_eq_right (by omega), Nat.cast_zero]
  · rw [ite_eq_right below, dite_eq_right (by omega), dite_eq_right (by omega), add_zero, Nat.cast_zero]

/-- Normalize each imported multiplication assertion into its byte column.
    The serialized inverse is interpreted in this artifact's BabyBear field. -/
theorem native_columns {w : Nat → ZMod babyBearModulus} {left right : Fin 16 → Nat}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (sources : ∀ i, w Variables.leftLimbs[i] = (left i : ZMod babyBearModulus) ∧
      w Variables.rightLimbs[i] = (right i : ZMod babyBearModulus))
    (bytes : ∀ i : Fin 16,
      w (99 + i.val) = ((left i % 256 : Nat) : ZMod babyBearModulus) ∧
      w (115 + i.val) = ((right i % 256 : Nat) : ZMod babyBearModulus)) :
    ∀ i : Fin 32, (multiplicationColumn left right i.val : ZMod babyBearModulus) + incoming w i =
      w (131 + i.val) + 65536 * outgoing w i := by
  intro i
  have gate := Verification.assertion_of_holds h ⟨19 + i.val, by rw [constraint_count]; omega⟩
  rw [column_shape, column_eval] at gate
  have terms : (∑ j ∈ Finset.range 16, termAt w i.val j) =
      (multiplicationColumn left right i.val : ZMod babyBearModulus) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => termAt w i.val j)]
    simp only [term_value sources bytes, multiplicationColumn, diagonal, Nat.cast_add,
      Nat.cast_sum, Finset.sum_add_distrib]
  rw [terms] at gate
  have scale : (65536 : ZMod babyBearModulus) * (-30720) = 1 := by decide
  unfold incoming outgoing carry Column.output at *
  have size := i.isLt
  by_cases last : i.val < 31
  · simp only [last, ↓reduceIte, ↓reduceDIte] at gate ⊢
    by_cases first : i.val = 0
    · simp only [first, ↓reduceIte, ↓reduceDIte] at gate ⊢
      linear_combination gate - (w 163 - w 131) * scale
    · simp only [first, ↓reduceIte, ↓reduceDIte] at gate ⊢
      linear_combination gate - (w (163 + i.val) - w (131 + i.val)) * scale
  · have index : i.val = 31 := by omega
    norm_num only [index, ↓reduceIte, ↓reduceDIte] at gate ⊢
    linear_combination gate

end Airbender.Bigint.Multiplication.Proofs
