import Airbender.Import.GKRProtocol.Source
import Airbender.Proofs.BabyBear
import Airbender.Proofs.UnifiedReduced
import Mathlib.Tactic.IntervalCases

namespace Airbender.Compiler.UnifiedPublicConstraints
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false

/-- At most one dispatcher contribution reaches a pooled query. The selected
binary-operation tag remains a separate decoder-derived input. -/
theorem one_hot_tags (operation : Source.BaseField) (different : operation ≠ 46)
    (control binary shift rom : Nat) (oneHotBound : control + binary + shift + rom ≤ 1) :
    ((control : Source.BaseField) + 8 * binary + 3 * shift + 34 * rom) ≠ 46 ∧
    (5 * (control : Source.BaseField) + 9 * binary + shift * operation) ≠ 46 ∧
    (51 * (control : Source.BaseField) + 9 * binary + shift * operation) ≠ 46 ∧
    (2 * (control : Source.BaseField) + 9 * binary + shift * operation) ≠ 46 := by
  have a : control ≤ 1 := by omega
  have b : binary ≤ 1 := by omega
  have c : shift ≤ 1 := by omega
  have d : rom ≤ 1 := by omega
  have g0 : (0 : Source.BaseField) ≠ 46 := by decide +kernel
  have g1 : (1 : Source.BaseField) ≠ 46 := by decide +kernel
  have g2 : (2 : Source.BaseField) ≠ 46 := by decide +kernel
  have g3 : (3 : Source.BaseField) ≠ 46 := by decide +kernel
  have g5 : (5 : Source.BaseField) ≠ 46 := by decide +kernel
  have g8 : (8 : Source.BaseField) ≠ 46 := by decide +kernel
  have g9 : (9 : Source.BaseField) ≠ 46 := by decide +kernel
  have g34 : (34 : Source.BaseField) ≠ 46 := by decide +kernel
  have g51 : (51 : Source.BaseField) ≠ 46 := by decide +kernel
  interval_cases control <;> interval_cases binary <;> interval_cases shift <;> interval_cases rom
  all_goals first | omega | simp_all

end Airbender.Compiler.UnifiedPublicConstraints

namespace Airbender.UnifiedReduced.Proofs
open Airbender.Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

-- This proof selects the 30 imported Boolean coordinates from the assertion list.
set_option maxHeartbeats 1600000 in
/-- Arithmetic assertions fix all native unified Boolean columns. -/
theorem unified_flags_of_assertions {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 10)}
    {w : Nat → ZMod p}
    (arithmetic : ∀ expression ∈ FlatOperation.constraints (importedConstraints setup),
      expression.eval (Verification.environment w) = 0) :
    ∀ i : Fin 30,
      w (#v[4, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
        26, 27, 28, 29, 52, 53, 54, 55, 56, 81, 122, 123, 124, 125][i]) = 0 ∨
      w (#v[4, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
        26, 27, 28, 29, 52, 53, 54, 55, 56, 81, 122, 123, 124, 125][i]) = 1 := by
  intro i
  have flag := arithmetic _ (List.get_mem _
    ⟨(#v[0, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104,
      105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119][i]),
      by rw [constraint_count]; fin_cases i <;> decide⟩)
  fin_cases i <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero, or_comm] at flag ⊢
  all_goals exact flag

open scoped BigOperators

/-- Active family dispatch has at most one selected sub-operation. The additional
    Family-2 rd-is-zero marker is excluded because it may accompany that operation. -/
theorem unified_dispatch_count_of_assertions {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 18)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (arithmetic : ∀ expression ∈ FlatOperation.constraints (importedConstraints setup),
      expression.eval (Verification.environment w) = 0)
    (active : w 4 = 1) :
    (∑ i : Fin 18, (w Variables.dispatchColumns[i]).val) ≤ 1 := by
  have definition := arithmetic _ (List.get_mem _ ⟨87, by rw [constraint_count]; decide⟩)
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, active] at definition
  have bits : ∀ i : Fin 18, w Variables.dispatchColumns[i] = 0 ∨ w Variables.dispatchColumns[i] = 1 := by
    intro i
    have flag := unified_flags_of_assertions arithmetic (#v[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19][i])
    fin_cases i <;> exact flag
  have total : (1 : ZMod p) = 0 ∨ (1 : ZMod p) = 1 := Or.inr rfl
  apply boolean_sum_le_one hp bits total
  simp [Variables.dispatchColumns, Fin.sum_univ_succ]
  linear_combination -definition

end Airbender.UnifiedReduced.Proofs

namespace Airbender.Compiler.UnifiedPublicConstraints
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

/-- Native arithmetic and the public operation tag exclude decoder rows. -/
theorem helper_not_decoder (setup : Table Source.BaseField (fields 10))
    (w : Nat → Source.BaseField)
    (arithmetic : ∀ expression ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints setup),
      expression.eval (Verification.environment w) = 0)
    (active : w 4 = 1) (operation : w 10 ≠ 46) :
    ∀ index : Fin 5, w (#v[82, 86, 95, 104, 113][index]) ≠ 46 := by
  have total := UnifiedReduced.Proofs.unified_dispatch_count_of_assertions (by decide +kernel) arithmetic active
  simp [UnifiedReduced.Variables.dispatchColumns, Fin.sum_univ_succ] at total
  have gate := arithmetic _ (List.get_mem _ ⟨39, by rw [UnifiedReduced.constraint_count]; decide⟩)
  simp [UnifiedReduced.importedConstraints, FlatOperation.constraints, _root_.Expression.eval,
    Verification.environment] at gate
  have romEq : w 81 = w 28 * w 54 := by linear_combination gate
  have romLe : (w 81).val ≤ (w 28).val := by
    have load : w 28 = 0 ∨ w 28 = 1 := by simpa using UnifiedReduced.Proofs.unified_flags_of_assertions arithmetic 18
    have rom : w 54 = 0 ∨ w 54 = 1 := by simpa using UnifiedReduced.Proofs.unified_flags_of_assertions arithmetic 22
    rw [romEq]
    rcases load with load | load <;> rcases rom with rom | rom
    all_goals norm_num [load, rom]
  let control := (w 21).val + (w 22).val + (w 23).val + (w 24).val
  have oneHotBound : control + (w 26).val + (w 27).val + (w 81).val ≤ 1 := by dsimp [control]; omega
  have tags := one_hot_tags (w 10) operation control (w 26).val (w 27).val (w 81).val oneHotBound
  have equation (index : Fin 5) := arithmetic _ (List.get_mem _
    ⟨(#v[45, 49, 58, 67, 76][index]), by rw [UnifiedReduced.constraint_count]; fin_cases index <;> norm_num⟩)
  have e0 := equation 0; have e1 := equation 1; have e2 := equation 2
  have e3 := equation 3; have e4 := equation 4
  simp [UnifiedReduced.importedConstraints, FlatOperation.constraints, _root_.Expression.eval,
    Verification.environment, active] at e0 e1 e2 e3 e4
  have ccast : (control : Source.BaseField) = w 21 + w 22 + w 23 + w 24 := by
    simp [control, Nat.cast_add]
  have t0 : w 82 = (control : Source.BaseField) + 8 * (w 26).val + 3 * (w 27).val + 34 * (w 81).val := by
    simp only [ccast, ZMod.natCast_zmod_val]
    linear_combination e0
  have t1 : w 86 = 5 * (control : Source.BaseField) + 9 * (w 26).val + (w 27).val * w 10 := by
    simp only [ccast, ZMod.natCast_zmod_val]
    linear_combination e1
  have t2 : w 95 = 5 * (control : Source.BaseField) + 9 * (w 26).val + (w 27).val * w 10 := by
    simp only [ccast, ZMod.natCast_zmod_val]
    linear_combination e2
  have t3 : w 104 = 51 * (control : Source.BaseField) + 9 * (w 26).val + (w 27).val * w 10 := by
    simp only [ccast, ZMod.natCast_zmod_val]
    linear_combination e3
  have t4 : w 113 = 2 * (control : Source.BaseField) + 9 * (w 26).val + (w 27).val * w 10 := by
    simp only [ccast, ZMod.natCast_zmod_val]
    linear_combination e4
  have n0 : w 82 ≠ 46 := by rw [t0]; exact tags.1
  have n1 : w 86 ≠ 46 := by rw [t1]; exact tags.2.1
  have n2 : w 95 ≠ 46 := by rw [t2]; exact tags.2.1
  have n3 : w 104 ≠ 46 := by rw [t3]; exact tags.2.2.1
  have n4 : w 113 ≠ 46 := by rw [t4]; exact tags.2.2.2
  intro index
  fin_cases index <;> assumption

end Airbender.Compiler.UnifiedPublicConstraints
