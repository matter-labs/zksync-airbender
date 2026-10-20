import Slop.Arithmetic.CarryChain

namespace Airbender.Arithmetic
open scoped BigOperators
set_option warningAsError true

def byteCross (a b : Nat) : Nat :=
  a % 256 * (b % 256) + 256 * (a % 256 * (b / 256) + a / 256 * (b % 256))

def byteHigh (a b : Nat) : Nat := a / 256 * (b / 256)

def diagonal {n : Nat} (f : Fin n → Fin n → Nat) (shift column : Nat) : Nat :=
  ∑ j, ∑ k, if j.val + k.val + shift = column then f j k else 0

/-- Bounded byte products grouped into 16-bit columns, before carry propagation. -/
def multiplicationColumn {n : Nat} (a b : Fin n → Nat) (column : Nat) : Nat :=
  diagonal (fun j k => byteCross (a j) (b k)) 0 column +
    diagonal (fun j k => byteHigh (a j) (b k)) 1 column

theorem byte_product (a b : Nat) : a * b = byteCross a b + 65536 * byteHigh a b := by
  have aa := Nat.mod_add_div a 256
  have bb := Nat.mod_add_div b 256
  unfold byteCross byteHigh
  calc
    _ = (a % 256 + 256 * (a / 256)) * (b % 256 + 256 * (b / 256)) := by rw [aa, bb]
    _ = _ := by ring

theorem byte_product_bounds {a b : Nat} (ha : a < 65536) (hb : b < 65536) :
    byteCross a b ≤ 33357825 ∧ byteHigh a b ≤ 65025 := by
  have al : a % 256 ≤ 255 := by have := Nat.mod_lt a (by decide : 0 < 256); omega
  have bl : b % 256 ≤ 255 := by have := Nat.mod_lt b (by decide : 0 < 256); omega
  have ah : a / 256 ≤ 255 := by omega
  have bh : b / 256 ≤ 255 := by omega
  have ll := Nat.mul_le_mul al bl
  have lh := Nat.mul_le_mul al bh
  have hl := Nat.mul_le_mul ah bl
  have hh := Nat.mul_le_mul ah bh
  unfold byteCross byteHigh
  constructor <;> omega

theorem diagonal_bound {n shift column bound : Nat} {f : Fin n → Fin n → Nat}
    (bounded : ∀ j k, f j k ≤ bound) : diagonal f shift column ≤ n * bound := by
  classical
  unfold diagonal
  calc
    _ ≤ ∑ _j : Fin n, bound := by
      apply Finset.sum_le_sum
      intro j _
      by_cases found : ∃ k : Fin n, j.val + k.val + shift = column
      · obtain ⟨k, selected⟩ := found
        rw [Finset.sum_eq_single k]
        · simpa only [selected, ↓reduceIte] using bounded j k
        · intro other _ different
          have unselected : j.val + other.val + shift ≠ column := by
            intro same
            apply different
            apply Fin.ext
            omega
          simp only [unselected, ↓reduceIte]
        · simp
      · have zeros : ∀ k : Fin n, j.val + k.val + shift ≠ column := by
          simpa only [not_exists] using found
        simp [zeros]
    _ = n * bound := by simp

theorem multiplication_column_bound {a b : Fin 16 → Nat} {column : Nat}
    (ha : ∀ i, a i < 65536) (hb : ∀ i, b i < 65536) :
    multiplicationColumn a b column ≤ 534765600 := by
  have cross := diagonal_bound (shift := 0) (column := column)
    (fun j k => (byte_product_bounds (ha j) (hb k)).1)
  have high := diagonal_bound (shift := 1) (column := column)
    (fun j k => (byte_product_bounds (ha j) (hb k)).2)
  unfold multiplicationColumn
  omega

theorem weighted_diagonal {n width shift : Nat} (radix : Nat) (f : Fin n → Fin n → Nat)
    (fits : ∀ j k : Fin n, j.val + k.val + shift < width) :
    (∑ i : Fin width, radix ^ i.val * diagonal f shift i.val) =
      ∑ j, ∑ k, radix ^ (j.val + k.val + shift) * f j k := by
  classical
  simp only [diagonal, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single ⟨j.val + k.val + shift, fits j k⟩]
  · simp
  · intro other _ different
    have unselected : j.val + k.val + shift ≠ other.val := by
      intro same
      apply different
      apply Fin.ext
      exact same.symm
    simp [unselected]
  · simp

/-- Summing bounded byte columns gives the full integer product; carries can
    then be eliminated with the shared carry-chain theorem. -/
theorem multiplication_columns {n : Nat} (a b : Fin n → Nat) :
    (∑ i : Fin (2 * n), 65536 ^ i.val * multiplicationColumn a b i.val) =
      (∑ j, 65536 ^ j.val * a j) * (∑ k, 65536 ^ k.val * b k) := by
  have fits (shift : Nat) (small : shift ≤ 1) (j k : Fin n) :
      j.val + k.val + shift < 2 * n := by have := j.isLt; have := k.isLt; omega
  simp only [multiplicationColumn, Nat.mul_add, Finset.sum_add_distrib]
  rw [weighted_diagonal _ _ (fits 0 (by decide)),
    weighted_diagonal _ _ (fits 1 (by decide))]
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ j, ∑ k, 65536 ^ (j.val + k.val) * (a j * b k) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      simp only [Nat.add_zero, pow_succ, byte_product (a j) (b k)]
      ring
    _ = _ := by
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum, pow_add]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

end Airbender.Arithmetic
