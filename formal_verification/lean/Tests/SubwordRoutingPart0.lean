import Tests.SubwordRoutingFixture

namespace Tests.SubwordRoutingPart0
open Airbender Verification SubwordMemory Tests.SubwordRoutingFixture
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem accepted_0 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨0,by decide⟩))
      (SubwordMemory.importedConstraints rom) := by
  simp [SubwordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
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
      Table.fromStatic,StaticTable.toTable,Expression.eval,environment,ProvableType.fromElements]
      using lookup_members ⟨0,by decide⟩ ⟨0,by decide⟩
  · simpa [Lookup.Contains,NativeSubwordLookup.lookup,Table.toRaw,NativeSubwordLookup.table,
      Table.fromStatic,StaticTable.toTable,Expression.eval,environment,ProvableType.fromElements]
      using lookup_members ⟨0,by decide⟩ ⟨1,by decide⟩

theorem accepted_1 :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨1,by decide⟩))
      (SubwordMemory.importedConstraints rom) := by
  simp [SubwordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) | (apply range16_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide +kernel) | skip
  · simp only [Lookup.Contains,fixed3,Table.toRaw,SubwordOffset.table,Table.fromStatic,
      StaticTable.toTable,ProvableType.fromElements]
    exact ⟨⟨851974,by decide⟩,by decide +kernel⟩
  · simp only [Lookup.Contains,fixed3,Table.toRaw,romSeparatorTable,Table.fromStatic,
      StaticTable.toTable,ProvableType.fromElements]
    exact ⟨⟨0,by decide⟩,by decide +kernel⟩
  · simpa [Lookup.Contains,NativeSubwordLookup.lookup,Table.toRaw,NativeSubwordLookup.table,
      Table.fromStatic,StaticTable.toTable,Expression.eval,environment,ProvableType.fromElements]
      using lookup_members ⟨1,by decide⟩ ⟨0,by decide⟩
  · simpa [Lookup.Contains,NativeSubwordLookup.lookup,Table.toRaw,NativeSubwordLookup.table,
      Table.fromStatic,StaticTable.toTable,Expression.eval,environment,ProvableType.fromElements]
      using lookup_members ⟨1,by decide⟩ ⟨1,by decide⟩

end Tests.SubwordRoutingPart0
