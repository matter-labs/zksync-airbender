import Slop.Blake2Round.ColumnG
import Slop.Blake2Round.Lookups
import Slop.Blake2Round.ArtifactChecks

set_option warningAsError true
-- one call's goals may not use every lemma of the shared simp set
set_option linter.unusedSimpArgs false

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

set_option maxHeartbeats 16000000 in
/-- The twelve Boolean assertions of column G call 1. -/
theorem column_g_flags_1 {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (k : Fin 12) :
    columnGBase (1 : Fin 4) w Blake2G.Variables.booleanColumns[1 + k.val] = 0 ∨
      columnGBase (1 : Fin 4) w Blake2G.Variables.booleanColumns[1 + k.val] = 1 := by
  have flag := Verification.assertion_of_holds h
    ⟨197 + 12 * (1 : Fin 4).val + k.val, by rw [constraint_count]; have size := k.isLt; simp; omega⟩
  fin_cases k
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, columnGBase, Blake2G.Variables.booleanColumns,
    mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] at flag ⊢
  all_goals exact flag

end Airbender.Blake2Round.Proofs
