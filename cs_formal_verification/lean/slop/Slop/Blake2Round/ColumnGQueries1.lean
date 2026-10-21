import Slop.Blake2Round.ColumnG
import Slop.Blake2Round.Lookups
import Slop.Blake2Round.ArtifactChecks
import Slop.Blake2Round.OpIndex
import Slop.Eval
import Slop.Blake2G.OpIndex

set_option warningAsError true
-- one call's goals may not use every lemma of the shared simp set
set_option linter.unusedSimpArgs false

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

set_option maxHeartbeats 16000000 in
/-- The eighteen XOR lookups of column G call 1. -/
theorem column_g_queries_1 {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (i : Fin 18) :
    ((FlatOperation.lookups (Blake2G.Proofs.mixingConstraints
      (Blake2G.setupTable (fun _ => Vector.replicate 7 0)))).get
        ⟨i.val, by rw [Blake2G.Proofs.mixing_lookup_count]; exact i.isLt⟩).Contains
      (Verification.environment (Blake2G.Proofs.assemble (columnGBase (1 : Fin 4) w))) := by
  have member := Verification.lookup_of_holds h
    ⟨2 + 18 * (1 : Fin 4).val + i.val, by rw [lookup_count]; have size := i.isLt; simp; omega⟩
  fin_cases i
  all_goals op_index at member ⊢
  all_goals apply padded_membership member
  all_goals ext j hj
  all_goals interval_cases j <;> eval_entry [columnGBase, Blake2G.Proofs.assemble, padXor]

end Airbender.Blake2Round.Proofs
