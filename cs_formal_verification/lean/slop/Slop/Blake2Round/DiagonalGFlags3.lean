import Slop.Blake2Round.DiagonalG
import Slop.Blake2Round.Lookups
import Slop.Blake2Round.ArtifactChecks
import Slop.Blake2Round.OpIndex
import Slop.Blake2G.OpIndex
import Slop.Blake2G.Soundness
import Mathlib.Tactic.ReduceModChar

set_option warningAsError true
-- one call's goals may not use every lemma of the shared simp set
set_option linter.unusedSimpArgs false

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

set_option maxHeartbeats 20000000 in
/-- The twelve Boolean assertions of diagonal G call 3. -/
theorem diagonal_g_flags_3 {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (k : Fin 12) :
    diagonalGBase (3 : Fin 4) w Blake2G.Variables.booleanColumns[1 + k.val] = 0 ∨
      diagonalGBase (3 : Fin 4) w Blake2G.Variables.booleanColumns[1 + k.val] = 1 := by
  have field := Blake2G.Proofs.serialized_field compatible
  subst p
  unfold babyBearModulus at *
  have flag := Verification.assertion_of_holds h
    ⟨245 + 12 * 3 + k.val, by rw [constraint_count]; have size := k.isLt; simp; omega⟩
  fin_cases k
  all_goals op_index at flag
  all_goals simp only [Expression.eval, Int.ofNat_eq_natCast, Nat.cast_one, Int.cast_one,
    Airbender.Verification.environment, one_mul, CharP.cast_eq_zero, Int.cast_zero, zero_add,
    Int.reduceNegSucc, Int.cast_neg, ← sub_eq_add_neg, mul_eq_zero, sub_eq_zero, diagonalGBase,
    Blake2G.Variables.booleanColumns, add_zero, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_succ, List.getElem_cons_zero, Nat.reduceAdd, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, mul_zero] at flag ⊢
  all_goals exact flag

end Airbender.Blake2Round.Proofs
