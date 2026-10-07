import Airbender.Review.Blake2G.Model
import Airbender.Proofs.Constraints
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2G.Proofs

/-- The twenty arithmetic assertions and eighteen XOR queries, selected from
    the imported artifact itself. Controller, addresses and timestamps are absent. -/
def mixingConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    List (FlatOperation (ZMod p)) :=
  ((importedConstraints setup).drop 3).take 20 ++ (importedConstraints setup).drop 35

theorem mixing_constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    (FlatOperation.constraints (mixingConstraints setup)).length = 20 := rfl

theorem mixing_lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    (FlatOperation.lookups (mixingConstraints setup)).length = 18 := rfl

theorem mixing_lookups {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    FlatOperation.lookups (mixingConstraints setup) =
      (FlatOperation.lookups (importedConstraints setup)).drop 3 := rfl

theorem mixing_holds {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (mixingConstraints setup) := by
  apply Verification.holds_append
  · exact Verification.holds_of_sublist h
      ((List.take_sublist 20 _).trans (List.drop_sublist 3 _))
  · exact Verification.holds_of_sublist h (List.drop_sublist 35 _)

def mixingModel {p : Nat} [Fact p.Prime] (control : Fin 512 → Vector Nat 7) :
    Verification.CircuitModel Input Words (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat
    (Verification.environment w) (mixingConstraints (setupTable control))
  represents := WordMapping

/-- Only the twelve arithmetic carries are needed by the reusable G proof. -/
theorem mixing_flags {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (mixingConstraints setup)) :
    ∀ i : Fin 12,
      w Variables.booleanColumns[1 + i.val] = 0 ∨ w Variables.booleanColumns[1 + i.val] = 1 := by
  intro i
  have flag := Verification.assertion_of_holds h
    ⟨8 + i.val, by rw [mixing_constraint_count]; have size := i.isLt; omega⟩
  fin_cases i <;> simp [mixingConstraints, importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, Variables.booleanColumns,
    mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] at flag ⊢
  all_goals exact flag

end Airbender.Blake2G.Proofs
