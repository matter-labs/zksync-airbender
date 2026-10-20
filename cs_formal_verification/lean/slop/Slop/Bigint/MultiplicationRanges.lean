import Slop.Bigint.Lookups
import Slop.Bigint.AdditiveFields

namespace Airbender.Bigint.Multiplication.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def rangeLimit (tag : Nat) : Nat := 2 ^ (tag - 13)

private theorem range_rows (index : Fin 1390592) {tag : Nat}
    (selected : (setupRow index).2.2 = tag) (tags : 22 ≤ tag ∧ tag ≤ 26) :
    (setupRow index).1 < rangeLimit tag ∧ (setupRow index).2.1 < rangeLimit tag := by
  have size := index.isLt
  have cases : tag = 22 ∨ tag = 23 ∨ tag = 24 ∨ tag = 25 ∨ tag = 26 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  all_goals unfold setupRow at selected ⊢
  all_goals dsimp only at selected ⊢
  all_goals split_ifs at selected ⊢ <;> simp [rangeLimit] at selected ⊢
  all_goals omega

/-- Interpret the five carry-range tags using actual Clean membership witnesses. -/
theorem range_values {p tag : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (tags : 22 ≤ tag ∧ tag ≤ 26)
    {entry : Vector (Expression (ZMod p)) 3} {env : Environment (ZMod p)}
    (h : (Lookup.mk setupTable.toRaw entry).Contains env)
    (selected : entry[2].eval env = (tag : ZMod p)) :
    (entry[0].eval env).val < rangeLimit tag ∧
      (entry[1].eval env).val < rangeLimit tag := by
  obtain ⟨i, first, second, rowTag⟩ := Bigint.Proofs.fixed_row_values hp (by omega) h selected
  have bounds := range_rows i rowTag tags
  have limit : rangeLimit tag ≤ 8192 := by
    have cases : tag = 22 ∨ tag = 23 ∨ tag = 24 ∨ tag = 25 ∨ tag = 26 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [first, second, ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)]
  exact bounds

/-- Native low-byte outputs are the remainders of the actual source limbs. -/
theorem source_low_bytes {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    ∀ i : Fin 16,
      w (99 + i.val) = (((w Variables.leftLimbs[i]).val % 256 : Nat) : ZMod p) ∧
      w (115 + i.val) = (((w Variables.rightLimbs[i]).val % 256 : Nat) : ZMod p) := by
  intro i
  have left := Verification.lookup_of_holds h ⟨34 + i.val,
    by rw [lookup_count]; have := i.isLt; omega⟩
  have right := Verification.lookup_of_holds h ⟨50 + i.val,
    by rw [lookup_count]; have := i.isLt; omega⟩
  fin_cases i
  all_goals have leftPair := Bigint.Proofs.low_byte_value hp left (by
    simp [Expression.eval, Verification.environment])
  all_goals have rightPair := Bigint.Proofs.low_byte_value hp right (by
    simp [Expression.eval, Verification.environment])
  all_goals constructor
  all_goals first
    | simpa [importedConstraints, FlatOperation.lookups, Expression.eval,
        Verification.environment, Variables.leftLimbs] using leftPair.2
    | simpa [importedConstraints, FlatOperation.lookups, Expression.eval,
        Verification.environment, Variables.rightLimbs] using rightPair.2

/-- No inverse assumption is needed to recover a source limb's two bytes. -/
theorem limb_bytes {p : Nat} [NeZero p] {source low : ZMod p}
    (bound : source.val < 65536) (lowValue : low = ((source.val % 256 : Nat) : ZMod p)) :
    low.val < 256 ∧ source.val / 256 < 256 ∧
      source = low + 256 * ((source.val / 256 : Nat) : ZMod p) := by
  have lowBound : source.val % 256 < 256 := Nat.mod_lt _ (by decide)
  refine ⟨?_, by omega, ?_⟩
  · rw [lowValue, ZMod.val_natCast]
    exact lt_of_le_of_lt (Nat.mod_le _ _) lowBound
  · rw [lowValue]
    have split : ((source.val % 256 + 256 * (source.val / 256) : Nat) : ZMod p) = source := by
      rw [Nat.mod_add_div, ZMod.natCast_zmod_val]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using split.symm

-- Carry i+1 is the ranged difference of intermediate i and product limb i.
def carry {p : Nat} (w : Nat → ZMod p) (i : Fin 31) : ZMod p :=
  (-30720) * (w (163 + i.val) - w (131 + i.val))

private def carryQuery (i : Fin 31) : Nat :=
  if i.val = 0 ∨ i.val = 30 then 66
  else if i.val = 1 ∨ i.val = 29 then 67
  else if i.val = 2 then 68 else if i.val = 3 then 69
  else if i.val = 27 then 70 else if i.val = 28 then 71
  else if i.val < 8 then 68 + i.val
  else if 23 ≤ i.val then 53 + i.val
  else 72 + i.val

private def carryTag (i : Fin 31) : Nat :=
  if i.val = 0 ∨ i.val = 30 then 22
  else if i.val = 1 ∨ i.val = 29 then 23
  else if i.val ≤ 3 ∨ 27 ≤ i.val then 24
  else if i.val ≤ 7 ∨ 23 ≤ i.val then 25 else 26

/-- Every multiplication carry is below 8192, derived from all 29 native
    carry queries (two queries range two carries each). -/
theorem carry_ranges {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    ∀ i : Fin 31, (carry w i).val < rangeLimit (carryTag i) := by
  intro i
  have member := Verification.lookup_of_holds h ⟨carryQuery i,
    by rw [lookup_count]; fin_cases i <;> decide⟩
  have tags : 22 ≤ carryTag i ∧ carryTag i ≤ 26 := by
    unfold carryTag
    split_ifs <;> decide
  fin_cases i
  all_goals have ranges := range_values hp tags member (by
    simp [carryTag, Expression.eval, Verification.environment])
  all_goals simp [carryTag, Expression.eval,
    Verification.environment] at ranges
  all_goals norm_num [carry, carryTag]
  all_goals solve
    | (convert ranges.1 using 1; congr 1; ring)
    | (convert ranges.2 using 1; congr 1; ring)

theorem carry_bounded {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) : ∀ i : Fin 31, (carry w i).val < 8192 := by
  intro i
  have bound := carry_ranges hp h i
  have limit : rangeLimit (carryTag i) ≤ 8192 := by
    unfold carryTag
    split_ifs <;> decide
  omega

end Airbender.Bigint.Multiplication.Proofs
