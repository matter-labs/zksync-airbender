module
public import Human.Circuits.Bigint.Multiplication
public import Proven.Bigint.EqualityGates
public import Proven.Bigint.OpIndex
public import Proven.CleanCore.Circuit.Operations

@[expose] public section

namespace Airbender.Bigint.Multiplication.Proofs
open Arithmetic
open scoped BigOperators
set_option warningAsError true

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
  rw [Shapes.write_holds h i]
  cases operation <;> norm_num [Operation.index, Variables.operations] at f0 f1 f2 f3 f4 f5 f6 <;>
    rw [f0, f1, f2, f3, f4, f5, f6] <;> ring

theorem native_high_sum {p : Nat} [Fact p.Prime] (hp : 8 ≤ p)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 62 = 1) : w 210 = ∑ i : Fin 16, w (147 + i.val) := by
  have flags := Additive.Proofs.selected_operations hp 3 h selected
  have low := flags 3
  have eq := flags 5
  norm_num [Variables.operations] at low eq
  have gate := Verification.assertion_of_holds h ⟨83, by rw [constraint_count]; decide⟩
  op_index at gate
  simp only [Expression.eval, Verification.environment, low, eq] at gate
  push_cast at gate
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
  have low := Verification.assertion_of_holds h ⟨89, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨90, by rw [constraint_count]; decide⟩
  cases operation <;> norm_num [Operation.index, Variables.operations] at f0 f1 f2 f3 f5 f6
  all_goals op_index at low high
  all_goals simp only [Expression.eval, Verification.environment, f0, f1, f2, f3, f5, f6] at low high
  all_goals push_cast at low high
  all_goals refine ⟨?_, high⟩
  · rw [zeroCheck] at low
    by_cases isZero : w 210 = 0 <;> simp only [isZero, ↓reduceIte] at low ⊢
    all_goals linear_combination -low
  · show w 57 = 0
    linear_combination -low

end Airbender.Bigint.Multiplication.Proofs
