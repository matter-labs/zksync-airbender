import Slop.Blake2G.ArtifactChecks
import Slop.Blake2G.Tables
import Slop.Blake2G.Fragment
import Human.Helpers.Properties
import Slop.Constraints

namespace Airbender.Blake2G.Proofs

set_option maxHeartbeats 1200000

/-- The imported arithmetic fragment supplies all eighteen sized XOR queries. -/
theorem data_lookups {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (mixingConstraints (setupTable control))) :
    ∀ q : Fin 18,
      let query := (FlatOperation.lookups (importedConstraints (setupTable control))).get
        ⟨q.val + 3, by rw [lookup_count]; have size := q.isLt; omega⟩
      let width := (#v[8, 8, 8, 8, 3, 9, 4, 3, 9, 4, 8, 8, 8, 8, 7, 9, 7, 9][q] : Nat)
      (query.entry.toArray[0]!.eval (Verification.environment w)).val < 2 ^ width ∧
      (query.entry.toArray[1]!.eval (Verification.environment w)).val < 2 ^ width ∧
      (query.entry.toArray[2]!.eval (Verification.environment w)).val < 2 ^ width ∧
      (query.entry.toArray[2]!.eval (Verification.environment w)).val =
        (query.entry.toArray[0]!.eval (Verification.environment w)).val ^^^
          (query.entry.toArray[1]!.eval (Verification.environment w)).val := by
  intro q
  have member := Verification.lookup_of_holds h
    ⟨q.val, by rw [mixing_lookup_count]; have size := q.isLt; omega⟩
  change ((FlatOperation.lookups (importedConstraints (setupTable control))).get
    ⟨q.val + 3, by rw [lookup_count]; have size := q.isLt; omega⟩).Contains
      (Verification.environment w) at member
  fin_cases q
  all_goals first
    | exact xor_lookup hp 0 member (by simp [importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment])
    | exact xor_lookup hp 1 member (by simp [importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment])
    | exact xor_lookup hp 2 member (by simp [importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment])
    | exact xor_lookup hp 3 member (by simp [importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment])
    | exact xor_lookup hp 4 member (by simp [importedConstraints, FlatOperation.lookups, Expression.eval, Verification.environment])

end Airbender.Blake2G.Proofs
