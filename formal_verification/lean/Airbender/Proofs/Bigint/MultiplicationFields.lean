import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Bigint.AdditiveFields

namespace Airbender.Bigint.Multiplication.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem merged_product {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 8)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 62 = 1 ∨ w 63 = 1) :
    ∀ i : Fin 16, w (194 + i.val) = w (131 + i.val) := by
  rcases selected with low | high
  all_goals first
    | have flags := Additive.Proofs.selected_operations hp 3 h low
    | have flags := Additive.Proofs.selected_operations hp 4 h high
  all_goals have f0 := flags 0
  all_goals have f1 := flags 1
  all_goals have f2 := flags 2
  all_goals have f3 := flags 3
  all_goals have f4 := flags 4
  all_goals have f5 := flags 5
  all_goals have f6 := flags 6
  all_goals norm_num [Variables.operations] at f0 f1 f2 f3 f4 f5 f6
  all_goals intro i
  all_goals have gate := Verification.assertion_of_holds h ⟨51 + i.val,
    by rw [constraint_count]; have := i.isLt; omega⟩
  all_goals fin_cases i
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, f0, f1, f2, f3, f4, f5, f6] at gate
  all_goals linear_combination gate

/-- Selected multiplication ranges all 32 product limbs, including the low half
    that shares its range query with the additive branches. -/
theorem product_ranges {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 8)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 62 = 1 ∨ w 63 = 1) :
    ∀ i : Fin 32, (w (131 + i.val)).val < limbBase := by
  have merged := merged_product hp h selected
  have low : ∀ i : Fin 16, (w (131 + i.val)).val < limbBase := by
    intro i
    rw [← merged i]
    exact Additive.Proofs.result_ranges h i
  have high : ∀ i : Fin 16, (w (147 + i.val)).val < limbBase := by
    intro i
    have member := Verification.lookup_of_holds h ⟨i.val,
      by rw [lookup_count]; have := i.isLt; omega⟩
    fin_cases i
    all_goals have bound := Verification.range16_bound member
    all_goals simpa [importedConstraints, FlatOperation.lookups, Expression.eval,
      Verification.environment] using bound
  intro i
  by_cases lower : i.val < 16
  · exact low ⟨i.val, lower⟩
  · have index : i.val - 16 < 16 := by have := i.isLt; omega
    have offset : 131 + i.val = 147 + (i.val - 16) := by omega
    rw [offset]
    exact high ⟨i.val - 16, index⟩

end Airbender.Bigint.Multiplication.Proofs
