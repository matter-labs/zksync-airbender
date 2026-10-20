import Slop.Bigint.MultiplicationProduct
import Slop.Bigint.MultiplicationWriteback
import Slop.Arithmetic.Digits

namespace Airbender.Bigint.Multiplication.Proofs
open Arithmetic
open scoped BigOperators
set_option warningAsError true

def halfValue (w : Nat → ZMod p) (offset : Nat) : Nat :=
  ∑ i : Fin 16, 65536 ^ i.val * (w (131 + offset + i.val)).val

theorem half_ranges {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (selected : w 62 = 1 ∨ w 63 = 1) :
    (∀ i : Fin 16, (w (131 + i.val)).val < 65536) ∧
      (∀ i : Fin 16, (w (147 + i.val)).val < 65536) := by
  have bound := product_ranges (by decide) h selected
  constructor
  · intro i; exact bound ⟨i.val, by have := i.isLt; omega⟩
  · intro i
    simpa only [Fin.val_mk, ← Nat.add_assoc, Nat.reduceAdd, limbBase] using
      bound ⟨16 + i.val, by have := i.isLt; omega⟩

theorem half_bounds {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (selected : w 62 = 1 ∨ w 63 = 1) :
    halfValue w 0 < 2 ^ 256 ∧ halfValue w 16 < 2 ^ 256 := by
  have ranges := half_ranges h selected
  have low := weighted_limb_bound (by decide : 0 < 65536) ranges.1
  have high := weighted_limb_bound (by decide : 0 < 65536) ranges.2
  have radix : 65536 ^ 16 = 2 ^ 256 := by decide
  rw [radix] at low high
  simpa only [halfValue, Nat.add_zero] using And.intro low high

theorem product_split (w : Nat → ZMod p) :
    (∑ i : Fin 32, 65536 ^ i.val * (w (131 + i.val)).val) =
      halfValue w 0 + 2 ^ 256 * halfValue w 16 := by
  rw [show 32 = 16 + 16 from rfl, Fin.sum_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd, pow_add, halfValue, Nat.add_zero,
    ← Nat.add_assoc, Finset.mul_sum, Nat.mul_assoc]
  norm_num only [show 65536 ^ 16 = 2 ^ 256 from by decide]

theorem high_zero {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (selected : w 62 = 1) :
    w 210 = 0 ↔ halfValue w 16 = 0 := by
  have highRanges := (half_ranges h (Or.inl selected)).2
  have sumBound : (∑ i : Fin 16, (w (147 + i.val)).val) < babyBearModulus := by
    have bounded : (∑ i : Fin 16, (w (147 + i.val)).val) ≤ 16 * 65535 := by
      calc
        _ ≤ ∑ _i : Fin 16, 65535 := Finset.sum_le_sum (by intro i _; have := highRanges i; omega)
        _ = _ := by simp
    exact lt_of_le_of_lt bounded (by decide)
  rw [native_high_sum (by decide) h selected]
  have nonwrapping := field_sum_zero sumBound
  have weighted := weighted_sum_zero (by decide : 0 < 65536)
    (limbs := fun i : Fin 16 => (w (147 + i.val)).val)
  simpa only [halfValue, Nat.reduceAdd] using nonwrapping.trans weighted.symm

/-- Full low/high arithmetic soundness for the BabyBear artifact. Byte,
    product and carry ranges follow from the native modeled-setup queries. -/
theorem soundness : Properties.Soundness (circuitModel (p := babyBearModulus)).relation spec := by
  intro input output w ⟨h, mapping⟩
  have selected : w 62 = 1 ∨ w 63 = 1 := by
    cases op : input.operation
    · exact Or.inl (by simpa [op, Operation.index, Variables.operations] using mapping.selected)
    · exact Or.inr (by simpa [op, Operation.index, Variables.operations] using mapping.selected)
  have ranges := half_ranges h selected
  have bounded := half_bounds h selected
  have actual := full_product h selected
  have inputLeft : (∑ i : Fin 16, 65536 ^ i.val * leftSource w i) = value input.left := by
    unfold value limbBase leftSource
    apply Finset.sum_congr rfl
    intro i _
    rw [mapping.left i]
  have inputRight : (∑ i : Fin 16, 65536 ^ i.val * rightSource w i) = value input.right := by
    unfold value limbBase rightSource
    apply Finset.sum_congr rfl
    intro i _
    rw [mapping.right i]
  rw [inputLeft, inputRight, product_split] at actual
  have split := product_halves (by decide : 0 < 2 ^ 256) bounded.1 actual
  have writes := native_writes (by decide) input.operation h mapping.selected
  have control := native_control (by decide) input.operation h mapping.selected
  have outRange : ∀ i : Fin 16, output.result[i] < limbBase := by
    intro i
    rw [mapping.result i, writes i]
    cases input.operation <;> first | exact ranges.1 i | exact ranges.2 i
  have outValue : value output.result = match input.operation with
      | .low => halfValue w 0 | .high => halfValue w 16 := by
    cases op : input.operation
    all_goals unfold value limbBase halfValue
    all_goals apply Finset.sum_congr rfl
    all_goals intro i _
    all_goals rw [mapping.result i, writes i]
    all_goals simp only [op, Nat.reduceAdd, Nat.add_zero]
  refine ⟨outRange, ?_, ?_⟩
  · rw [outValue]
    cases input.operation
    · exact split.1.symm
    · exact split.2.1.symm
  · rw [mapping.control, control.1, control.2]
    cases op : input.operation
    · have low : w 62 = 1 := by simpa [op, Operation.index, Variables.operations] using mapping.selected
      have zero := high_zero h low
      by_cases overflow : 2 ^ 256 ≤ value input.left * value input.right
      · have nonzero : w 210 ≠ 0 := by
          intro bad
          exact (split.2.2.mp overflow) (zero.mp bad)
        simp only [nonzero, ↓reduceIte, if_pos overflow,
          show (1 : ZMod babyBearModulus).val = 1 from by decide, ZMod.val_zero]
      · have highZero : halfValue w 16 = 0 := by
          by_contra nonzero
          exact overflow (split.2.2.mpr nonzero)
        have isZero := zero.mpr highZero
        simp only [isZero, ↓reduceIte, if_neg overflow, ZMod.val_zero]
    · simp only [ZMod.val_zero]

end Airbender.Bigint.Multiplication.Proofs
