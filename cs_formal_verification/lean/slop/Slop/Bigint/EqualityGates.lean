module
public import Human.Circuits.Bigint.Equality
public import Slop.Bigint.AdditiveFields
public import Slop.Bigint.OpIndex
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

namespace Airbender.Bigint.Equality.Proofs
open Arithmetic
open scoped BigOperators
set_option warningAsError true

def carryColumn (i : Nat) : Nat := 82 + i

theorem native_steps {p : Nat} [Fact p.Prime] (hp : 8 ≤ p)
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
  have gate := Shapes.step_holds h i
  rw [Shapes.step_eval, f0, f1, f2, f5, f6] at gate
  rw [Shapes.left_column, Shapes.right_column]
  unfold carryColumn
  by_cases first : i.val = 0 <;> simp only [first, ↓reduceIte] at gate ⊢ <;>
    linear_combination gate

theorem native_results {p : Nat} [Fact p.Prime] (hp : 8 ≤ p)
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
  rw [Shapes.definition_holds h i, Shapes.write_holds h i, f0, f1, f2, f3, f4, f5, f6]
  constructor <;> ring

theorem native_sum {p : Nat} [Fact p.Prime] (hp : 8 ≤ p)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 64 = 1) : w 210 = ∑ i : Fin 16, w (67 + i.val) := by
  have flags := Additive.Proofs.selected_operations hp 5 h selected
  have f3 := flags 3
  have f5 := flags 5
  norm_num [Variables.operations] at f3 f5
  have gate := Verification.assertion_of_holds h ⟨83, by rw [constraint_count]; decide⟩
  op_index at gate
  simp only [Expression.eval, Verification.environment, f3, f5] at gate
  push_cast at gate
  norm_num [Fin.sum_univ_succ]
  linear_combination gate

theorem native_zero_check {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    w 212 = if w 210 = 0 then 1 else 0 := by
  have definition := Verification.assertion_of_holds h ⟨85, by rw [constraint_count]; decide⟩
  have zero := Verification.assertion_of_holds h ⟨86, by rw [constraint_count]; decide⟩
  have inverse := Verification.assertion_of_holds h ⟨87, by rw [constraint_count]; decide⟩
  op_index at definition zero inverse
  simp only [Expression.eval, Verification.environment] at definition zero inverse
  push_cast at definition zero inverse
  have copy : w 214 = w 212 := by linear_combination definition
  rw [copy] at zero inverse
  simp only [one_mul] at zero
  by_cases isZero : w 210 = 0
  · simp only [isZero, ↓reduceIte]
    rw [isZero] at inverse
    linear_combination inverse
  · simp only [isZero, ↓reduceIte]
    exact (mul_eq_zero.mp zero).resolve_left isZero

theorem native_control {p : Nat} [Fact p.Prime] (hp : 8 ≤ p)
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
  op_index at response low high
  simp only [Expression.eval, Verification.environment, f0, f1, f2, f3, f5, f6] at response low high
  push_cast at response low high
  refine ⟨?_, high⟩
  linear_combination -response - low

end Airbender.Bigint.Equality.Proofs
