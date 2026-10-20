import Slop.Blake2Round.DiagonalG
import Slop.Blake2Round.Lookups
import Slop.Blake2Round.ArtifactChecks
import Slop.Blake2G.Soundness
import Mathlib.Tactic.ReduceModChar

set_option warningAsError true
-- one call's goals may not use every lemma of the shared simp set
set_option linter.unusedSimpArgs false

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

set_option maxHeartbeats 20000000 in
/-- The twelve Boolean assertions of diagonal G call 0. -/
theorem diagonal_g_flags_0 {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (k : Fin 12) :
    diagonalGBase (0 : Fin 4) w Blake2G.Variables.booleanColumns[1 + k.val] = 0 ∨
      diagonalGBase (0 : Fin 4) w Blake2G.Variables.booleanColumns[1 + k.val] = 1 := by
  have field := Blake2G.Proofs.serialized_field compatible
  subst p
  unfold babyBearModulus at *
  have flag := Verification.assertion_of_holds h
    ⟨245 + 12 * (0 : Fin 4).val + k.val, by rw [constraint_count]; have size := k.isLt; simp; omega⟩
  fin_cases k
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, diagonalGBase, Blake2G.Variables.booleanColumns,
    mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] at flag ⊢
  all_goals exact flag

end Airbender.Blake2Round.Proofs
