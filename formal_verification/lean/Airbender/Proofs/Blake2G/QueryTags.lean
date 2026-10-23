import Airbender.Proofs.Blake2G.ArtifactChecks
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2G.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 1200000

def dataQueryKinds : Vector (Fin 5) 18 :=
  #v[0, 0, 0, 0, 1, 4, 2, 1, 4, 2, 0, 0, 0, 0, 3, 4, 3, 4]

/-- Check the native arithmetic-query tags without depending on table soundness. -/
theorem data_query_tag {p : Nat} [Fact p.Prime]
    (setup : Table (ZMod p) (fields 9)) (env : Environment (ZMod p)) (q : Fin 18) :
    (((FlatOperation.lookups (importedConstraints setup)).get
      ⟨q.val + 3, by rw [lookup_count]; have := q.isLt; omega⟩).entry.toArray[8]!).eval env =
      ((#v[4, 17, 18, 19, 20][dataQueryKinds[q]] : Nat) : ZMod p) := by
  fin_cases q
  all_goals simp [importedConstraints, FlatOperation.lookups, Expression.eval, dataQueryKinds]

/-- All eighteen native arithmetic queries use the supplied table. -/
theorem data_query_table {p : Nat} [Fact p.Prime]
    (setup : Table (ZMod p) (fields 9)) (q : Fin 18) :
    ((FlatOperation.lookups (importedConstraints setup)).get
      ⟨q.val + 3, by rw [lookup_count]; have := q.isLt; omega⟩).table = setup.toRaw := by
  fin_cases q <;> rfl

theorem data_query_width (q : Fin 18) :
    (#v[8, 3, 4, 7, 9][dataQueryKinds[q]] : Nat) =
      #v[8, 8, 8, 8, 3, 9, 4, 3, 9, 4, 8, 8, 8, 8, 7, 9, 7, 9][q] := by
  fin_cases q <;> rfl

end Airbender.Blake2G.Proofs
