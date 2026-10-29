import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Circuits.Bigint.Equality
import Airbender.Proofs.Bigint.AdditiveFields

namespace Airbender.Bigint.Equality.Proofs
open Arithmetic
open scoped BigOperators
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def carryColumn (i : Nat) : Nat := 82 + i

theorem native_steps {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 8)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 64 = 1) : ∀ i : Fin 16,
    w (67 + i.val) + w Variables.rightLimbs[i] + (if i.val = 0 then 0 else w (carryColumn i.val)) =
      w Variables.leftLimbs[i] + 65536 * w (83 + i.val) := by
  have flags := Additive.Proofs.selected_operations hp 5 h selected
  have f0 := flags 0
  have f1 := flags 1
  have f2 := flags 2
  have f5 := flags 5
  have f6 := flags 6
  norm_num [Variables.operations] at f0 f1 f2 f5 f6
  intro i
  have gate := Verification.assertion_of_holds h ⟨3 + i.val,
    by rw [constraint_count]; have := i.isLt; omega⟩
  fin_cases i
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, f0, f1, f2, f5, f6] at gate
  all_goals norm_num [Variables.leftLimbs, Variables.rightLimbs, carryColumn]
  all_goals linear_combination gate

theorem native_results {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 8)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 64 = 1) : ∀ i : Fin 16,
    w (194 + i.val) = w (67 + i.val) ∧ w Variables.writtenLimbs[i] = w Variables.leftLimbs[i] := by
  have flags := Additive.Proofs.selected_operations hp 5 h selected
  have f0 := flags 0
  have f1 := flags 1
  have f2 := flags 2
  have f3 := flags 3
  have f4 := flags 4
  have f5 := flags 5
  have f6 := flags 6
  norm_num [Variables.operations] at f0 f1 f2 f3 f4 f5 f6
  intro i
  have definition := Verification.assertion_of_holds h ⟨51 + i.val,
    by rw [constraint_count]; have := i.isLt; omega⟩
  have write := Verification.assertion_of_holds h ⟨67 + i.val,
    by rw [constraint_count]; have := i.isLt; omega⟩
  fin_cases i
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, f0, f1, f2, f3, f4, f5, f6] at definition write
  all_goals norm_num [Variables.leftLimbs, Variables.writtenLimbs]
  all_goals constructor
  all_goals first | linear_combination definition | linear_combination -write

theorem native_sum {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 8)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 64 = 1) : w 210 = ∑ i : Fin 16, w (67 + i.val) := by
  have flags := Additive.Proofs.selected_operations hp 5 h selected
  have f3 := flags 3
  have f5 := flags 5
  norm_num [Variables.operations] at f3 f5
  have gate := Verification.assertion_of_holds h ⟨83, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, f3, f5] at gate
  norm_num [Fin.sum_univ_succ]
  linear_combination gate

theorem native_zero_check {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    w 212 = if w 210 = 0 then 1 else 0 := by
  have definition := Verification.assertion_of_holds h ⟨85, by rw [constraint_count]; decide⟩
  have zero := Verification.assertion_of_holds h ⟨86, by rw [constraint_count]; decide⟩
  have inverse := Verification.assertion_of_holds h ⟨87, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at definition zero inverse
  have copy : w 214 = w 212 := by linear_combination definition
  rw [copy] at zero inverse
  by_cases isZero : w 210 = 0
  · simp only [isZero, ↓reduceIte]
    rw [isZero] at inverse
    linear_combination inverse
  · simp only [isZero, ↓reduceIte]
    exact zero.resolve_left isZero

theorem native_control {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 8)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 64 = 1) : w 57 = w 212 * (1 - w 98) ∧ w 58 = 0 := by
  have flags := Additive.Proofs.selected_operations hp 5 h selected
  have f0 := flags 0
  have f1 := flags 1
  have f2 := flags 2
  have f3 := flags 3
  have f5 := flags 5
  have f6 := flags 6
  norm_num [Variables.operations] at f0 f1 f2 f3 f5 f6
  have response := Verification.assertion_of_holds h ⟨88, by rw [constraint_count]; decide⟩
  have low := Verification.assertion_of_holds h ⟨89, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨90, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, f0, f1, f2, f3, f5, f6] at response low high
  refine ⟨?_, high⟩
  linear_combination -response - low

end Airbender.Bigint.Equality.Proofs
