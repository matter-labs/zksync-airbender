import Airbender.Proofs.Blake2G.RawXorLookup
import Airbender.Proofs.Blake2G.QueryTags
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Blake2G.ArtifactChecks
import Airbender.Proofs.Blake2G.Tables
import Airbender.Proofs.Blake2G.Fragment
import Airbender.Review.Helpers.Properties
import Airbender.Proofs.Constraints

namespace Airbender.Blake2G.Proofs

set_option maxHeartbeats 1200000

/-- The imported arithmetic fragment supplies all eighteen sized XOR queries. -/
theorem data_lookups_of_queries {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    {control : Fin 512 → Vector Nat 7} {w : Nat → ZMod p}
    (h : QueryHolds (setupTable control) w) :
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
  have member := h q
  change ((FlatOperation.lookups (importedConstraints (setupTable control))).get
    ⟨q.val + 3, by rw [lookup_count]; have size := q.isLt; omega⟩).Contains
      (Verification.environment w) at member
  have result := xor_lookup_raw hp dataQueryKinds[q] member
    (data_query_table (setupTable control) q)
    (data_query_tag (setupTable control) (Verification.environment w) q)
  simpa only [data_query_width] using result

theorem data_lookups {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
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
  exact data_lookups_of_queries hp (query_holds_of_holds h)

end Airbender.Blake2G.Proofs
