import Tests.SubwordDecoderFixture

namespace Tests.SubwordOddX0Row
open Airbender Verification Arithmetic Trace SubwordMemory
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

abbrev rom := Tests.SubwordDecoderFixture.rom

/-- Actual native odd LH-to-x0 row. No native equation or lookup is removed. -/
def values : Array Nat := #[0,0,4,0,1,1,0,0,1,0,0,1,0,4,0,8,0,3,64,3,64,0,3,3,1,1,1,0,0,0,0,64,32769,32769,1,0,0,0,0,0,0,0,0,0,0,0,32769,0,0,0,0,0,491521,0,0,45,0,0,0,0,0,0,0,0,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,0]
def assignment (column : Nat) : ZMod mersenne31Modulus := (values[column]?.getD 0 : Nat)

theorem native_constraints :
    FlatOperation.ConstraintsHoldFlat (environment assignment) (SubwordMemory.importedConstraints rom) := by
  simp [SubwordMemory.importedConstraints,FlatOperation.ConstraintsHoldFlat,Expression.eval,
    environment,assignment,values]
  all_goals repeat' apply And.intro
  all_goals first | (apply timestamp19_contains; decide) | (apply range16_contains; decide) |
    (refine Eq.trans (b := (0 : ZMod mersenne31Modulus)) ?_ rfl; decide +kernel) | skip
  · simp only [Lookup.Contains,fixed3,Table.toRaw,SubwordOffset.table,Table.fromStatic,
      StaticTable.toTable,ProvableType.fromElements]
    exact ⟨⟨1638403,by decide⟩,by decide +kernel⟩
  · simp only [Lookup.Contains,fixed3,Table.toRaw,romSeparatorTable,Table.fromStatic,
      StaticTable.toTable,ProvableType.fromElements]
    exact ⟨⟨64,by decide⟩,by decide +kernel⟩
  · have member : (NativeSubwordLookup.table rom).Contains #[]
        (#v[491521,0,0,45] : Vector (ZMod mersenne31Modulus) 4) := by
      apply (NativeLookupProofs.load_membership rom #v[491521,0,0]).mpr
      exact ⟨⟨491521,by decide⟩,by decide +kernel⟩
    simpa [Lookup.Contains,NativeSubwordLookup.lookup,Table.toRaw,NativeSubwordLookup.table,
      Table.fromStatic,StaticTable.toTable,Expression.eval,environment,ProvableType.fromElements,
      assignment,values] using member
  · simpa [Lookup.Contains,NativeSubwordLookup.lookup,Table.toRaw,NativeSubwordLookup.table,
      Table.fromStatic,StaticTable.toTable,Expression.eval,environment,ProvableType.fromElements,
      assignment,values,Tests.SubwordDecoderFixture.assignment,Tests.SubwordDecoderFixture.values]
      using Tests.SubwordDecoderFixture.lookup_members ⟨3,by decide⟩ ⟨1,by decide⟩

end Tests.SubwordOddX0Row
