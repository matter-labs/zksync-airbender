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
/-- The eighteen XOR lookups of diagonal G call 1. -/
theorem diagonal_g_queries_1 {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (i : Fin 18) :
    ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
        ⟨i.val, by rw [Blake2G.Proofs.mixing_lookup_count]; exact i.isLt⟩).Contains
      (Verification.environment (Blake2G.Proofs.assemble (diagonalGBase (1 : Fin 4) w))) := by
  have field := Blake2G.Proofs.serialized_field compatible
  subst p
  unfold babyBearModulus at *
  have member := Verification.lookup_of_holds h
    ⟨74 + 18 * (1 : Fin 4).val + i.val, by rw [lookup_count]; have size := i.isLt; simp; omega⟩
  fin_cases i
  all_goals apply padded_membership member
  all_goals ext j hj
  all_goals interval_cases j <;>
    simp [Expression.eval, Verification.environment, diagonalGBase, columnGAssignment,
        columnGBase, Blake2G.Proofs.assemble, Blake2G.Proofs.secondAlo,
        Blake2G.Proofs.secondAhi, Blake2G.Proofs.secondClo, Blake2G.Proofs.secondChi,
        Blake2G.Proofs.firstAlo, Blake2G.Proofs.firstAhi, Blake2G.Proofs.firstClo,
        Blake2G.Proofs.firstChi, padXor]
  all_goals ring_nf <;> reduce_mod_char <;> ring_nf <;> reduce_mod_char

end Airbender.Blake2Round.Proofs
