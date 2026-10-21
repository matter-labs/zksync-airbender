import Tests.SubwordHistoryFixture

namespace Tests.SubwordHistoryStale
open Airbender Verification Arithmetic Trace SubwordMemory Tests.SubwordHistoryRows Tests.SubwordHistoryFixture
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def staleAssignment (column : Nat) : ZMod mersenne31Modulus :=
  if column = 74 then 0 else assignment ⟨7,by decide⟩ column

/-- Local constraints alone still accept the stale alias timestamp. -/
theorem stale_local_constraints :
    FlatOperation.ConstraintsHoldFlat (environment staleAssignment) (SubwordMemory.importedConstraints rom) := by
  simp [SubwordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, staleAssignment, assignment, aliasValues]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) | (apply range16_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide +kernel) | skip
  · simp only [Lookup.Contains,fixed3,Table.toRaw,SubwordOffset.table,Table.fromStatic,
      StaticTable.toTable,ProvableType.fromElements]
    exact ⟨⟨524288,by decide⟩,by decide +kernel⟩
  · simp only [Lookup.Contains,fixed3,Table.toRaw,romSeparatorTable,Table.fromStatic,
      StaticTable.toTable,ProvableType.fromElements]
    exact ⟨⟨0,by decide⟩,by decide +kernel⟩
  · simpa [Lookup.Contains,NativeSubwordLookup.lookup,Table.toRaw,NativeSubwordLookup.table,
      Table.fromStatic,StaticTable.toTable,Expression.eval,environment,ProvableType.fromElements,
      staleAssignment,assignment,aliasValues,Tests.SubwordDecoderFixture.assignment,Tests.SubwordDecoderFixture.values]
      using Tests.SubwordDecoderFixture.lookup_members ⟨0,by decide⟩ ⟨0,by decide⟩
  · simpa [Lookup.Contains,NativeSubwordLookup.lookup,Table.toRaw,NativeSubwordLookup.table,
      Table.fromStatic,StaticTable.toTable,Expression.eval,environment,ProvableType.fromElements,
      staleAssignment,assignment,aliasValues,Tests.SubwordDecoderFixture.assignment,Tests.SubwordDecoderFixture.values]
      using Tests.SubwordDecoderFixture.lookup_members ⟨0,by decide⟩ ⟨1,by decide⟩

def staleTrace : Data mersenne31Modulus SubwordMemoryFamily :=
  { trace ⟨7,by decide⟩ with rows := [⟨.subwordMemory,staleAssignment⟩] }

end Tests.SubwordHistoryStale
