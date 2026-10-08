import Airbender.Review.Bigint.Additive
import Airbender.Proofs.Bigint.Control

namespace Airbender.Bigint.Additive.Proofs
open Arithmetic
open scoped BigOperators
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option warningAsError true

theorem selected_operations {p : Nat} [Fact p.Prime] (hp : 8 ≤ p)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p} (chosen : Fin 7)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w Variables.operations[chosen] = 1) :
    ∀ i : Fin 7, w Variables.operations[i] = if i = chosen then 1 else 0 := by
  have total := Control.Proofs.opcode_exclusivity hp h
  have one : (w Variables.operations[chosen]).val = 1 := by
    rw [selected]
    exact ZMod.val_one (by omega)
  intro i
  by_cases same : i = chosen
  · simpa [same] using selected
  · simp only [same, ↓reduceIte]
    have zero := sum_le_one_exclusive total chosen one i same
    calc
      _ = ((w Variables.operations[i]).val : ZMod p) := (ZMod.natCast_zmod_val _).symm
      _ = 0 := by rw [zero, Nat.cast_zero]

theorem carry_bits {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 3)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    ∀ i : Fin 16, w (83 + i.val) = 0 ∨ w (83 + i.val) = 1 := by
  intro i
  have flag := Verification.assertion_of_holds h ⟨100 + i.val,
    by rw [constraint_count]; have := i.isLt; omega⟩
  fin_cases i <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] at flag ⊢
  all_goals exact flag

theorem result_ranges {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 3)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    ∀ i : Fin 16, (w (194 + i.val)).val < limbBase := by
  intro i
  have member := Verification.lookup_of_holds h ⟨16 + i.val,
    by rw [lookup_count]; have := i.isLt; omega⟩
  fin_cases i
  all_goals have bound := Verification.range16_bound member
  all_goals simpa [importedConstraints, FlatOperation.lookups, Expression.eval,
    Verification.environment] using bound

end Airbender.Bigint.Additive.Proofs
