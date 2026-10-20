import Human.Circuits.Bigint.Multiplication
import Slop.Bigint.EqualityGates

namespace Airbender.Bigint.Multiplication.Proofs
open Arithmetic
open scoped BigOperators
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem native_writes {p : Nat} [Fact p.Prime] (hp : 8 ≤ p)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p} (operation : Operation)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w Variables.operations[operation.index] = 1) :
    ∀ i : Fin 16, w Variables.writtenLimbs[i] =
      (match operation with | .low => w (131 + i.val) | .high => w (147 + i.val)) := by
  have flags := Additive.Proofs.selected_operations hp operation.index h selected
  have f0 := flags 0
  have f1 := flags 1
  have f2 := flags 2
  have f3 := flags 3
  have f4 := flags 4
  have f5 := flags 5
  have f6 := flags 6
  intro i
  have gate := Verification.assertion_of_holds h ⟨67 + i.val,
    by rw [constraint_count]; have := i.isLt; omega⟩
  cases operation <;> norm_num [Operation.index, Variables.operations] at f0 f1 f2 f3 f4 f5 f6
  all_goals fin_cases i
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, f0, f1, f2, f3, f4, f5, f6] at gate
  all_goals norm_num [Variables.writtenLimbs]
  all_goals linear_combination -gate

theorem native_high_sum {p : Nat} [Fact p.Prime] (hp : 8 ≤ p)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 62 = 1) : w 210 = ∑ i : Fin 16, w (147 + i.val) := by
  have flags := Additive.Proofs.selected_operations hp 3 h selected
  have low := flags 3
  have eq := flags 5
  norm_num [Variables.operations] at low eq
  have gate := Verification.assertion_of_holds h ⟨83, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, low, eq] at gate
  norm_num [Fin.sum_univ_succ]
  linear_combination gate

theorem native_control {p : Nat} [Fact p.Prime] (hp : 8 ≤ p)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p} (operation : Operation)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w Variables.operations[operation.index] = 1) :
    w 57 = (match operation with | .low => if w 210 = 0 then 0 else 1 | .high => 0) ∧
      w 58 = 0 := by
  have flags := Additive.Proofs.selected_operations hp operation.index h selected
  have f0 := flags 0
  have f1 := flags 1
  have f2 := flags 2
  have f3 := flags 3
  have f5 := flags 5
  have f6 := flags 6
  have zeroCheck := Equality.Proofs.native_zero_check h
  have low := Verification.assertion_of_holds h ⟨90, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨91, by rw [constraint_count]; decide⟩
  cases operation <;> norm_num [Operation.index, Variables.operations] at f0 f1 f2 f3 f5 f6
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, f0, f1, f2, f3, f5, f6] at low high
  all_goals refine ⟨?_, high⟩
  · rw [zeroCheck] at low
    by_cases isZero : w 210 = 0 <;> simp only [isZero, ↓reduceIte] at low ⊢
    all_goals linear_combination -low
  · exact low

end Airbender.Bigint.Multiplication.Proofs
