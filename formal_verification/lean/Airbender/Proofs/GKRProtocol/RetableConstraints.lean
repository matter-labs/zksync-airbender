import Airbender.Proofs.GKRProtocol.CleanBindings
import Airbender.Proofs.GKRProtocol.CleanPrimitiveLookups

namespace Airbender.Compiler
set_option warningAsError true

/-- Retable precisely the authored vector queries while retaining every scalar
lookup and every arithmetic assertion. No equality of table records is needed. -/
theorem retable_constraints
    (before after : Table Source.BaseField (fields width))
    (queries : List (Vector (_root_.Expression Source.BaseField) width))
    (fixedBefore fixedAfter : List (Lookup Source.BaseField))
    (oldOperations newOperations : List (FlatOperation Source.BaseField))
    (arithmetic : FlatOperation.constraints newOperations = FlatOperation.constraints oldOperations)
    (oldLookups : FlatOperation.lookups oldOperations =
      fixedBefore ++ queries.map (fun query => Lookup.mk before.toRaw query) ++ fixedAfter)
    (newLookups : FlatOperation.lookups newOperations =
      fixedBefore ++ queries.map (fun query => Lookup.mk after.toRaw query) ++ fixedAfter)
    (environment : Environment Source.BaseField)
    (native : FlatOperation.ConstraintsHoldFlat environment oldOperations)
    (refines : ∀ query ∈ queries,
      before.Contains (environment.data.getTable before) (query.map (fun field => field.eval environment)) →
      after.Contains (environment.data.getTable after) (query.map (fun field => field.eval environment))) :
    FlatOperation.ConstraintsHoldFlat environment newOperations := by
  obtain ⟨assertions, lookups⟩ := FlatOperation.constraintsHoldFlat_iff_forall_mem.mp native
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  constructor
  · rw [arithmetic]
    exact assertions
  · intro lookup member
    rw [newLookups] at member
    rcases List.mem_append.mp member with earlier | later
    · rcases List.mem_append.mp earlier with scalar | vector
      · exact lookups lookup (oldLookups ▸ List.mem_append_left _ (List.mem_append_left _ scalar))
      · obtain ⟨query, included, rfl⟩ := List.mem_map.mp vector
        have present := lookups (Lookup.mk before.toRaw query)
          (oldLookups ▸ List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨query, included, rfl⟩)))
        exact clean_vector_lookup after query environment (refines query included present)
    · exact lookups lookup (oldLookups ▸ List.mem_append_right _ later)

end Airbender.Compiler
