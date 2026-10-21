import Tests.SubwordDecoder
import Airbender.Review.Trace.Families.SubwordMemory.History

namespace Tests.SubwordHistoryRows
open Airbender Verification Arithmetic Trace SubwordMemory
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

abbrev rom := Tests.SubwordDecoderFixture.rom

/-- The extra LB aliases rs1=rd=1. Port two consumes the readonly source
    refresh at clock four. All original seven decoder rows stay unchanged. -/
def aliasValues : Array Nat := #[0,0,4,0,1,1,0,1,0,0,0,0,0,4,0,8,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,32769,32769,1,1,0,0,0,65534,65535,33022,4660,33022,65534,65535,32769,0,98556,0,98556,0,0,33022,4660,46,33022,65534,65535,45,65534,65535,65534,65535,1227138194,0,2147450879,0,0,0,1,0,0,1,4,0,1,0]

def assignment (sample : Fin 8) (column : Nat) : ZMod mersenne31Modulus :=
  if sample.val = 7 then ((aliasValues[column]?.getD 0 : Nat) : ZMod mersenne31Modulus)
  else Tests.SubwordDecoderFixture.assignment ⟨sample.val % 7, Nat.mod_lt _ (by decide)⟩ column

private theorem alias_constraints :
    FlatOperation.ConstraintsHoldFlat (environment (assignment ⟨7,by decide⟩))
      (SubwordMemory.importedConstraints rom) := by
  simp [SubwordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, aliasValues]
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
      assignment,aliasValues,Tests.SubwordDecoderFixture.assignment,Tests.SubwordDecoderFixture.values]
      using Tests.SubwordDecoderFixture.lookup_members ⟨0,by decide⟩ ⟨0,by decide⟩
  · simpa [Lookup.Contains,NativeSubwordLookup.lookup,Table.toRaw,NativeSubwordLookup.table,
      Table.fromStatic,StaticTable.toTable,Expression.eval,environment,ProvableType.fromElements,
      assignment,aliasValues,Tests.SubwordDecoderFixture.assignment,Tests.SubwordDecoderFixture.values]
      using Tests.SubwordDecoderFixture.lookup_members ⟨0,by decide⟩ ⟨1,by decide⟩

theorem native_constraints (sample : Fin 8) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment sample))
      (SubwordMemory.importedConstraints rom) := by
  fin_cases sample
  · exact Tests.SubwordDecoder.native_constraints ⟨0,by decide⟩
  · exact Tests.SubwordDecoder.native_constraints ⟨1,by decide⟩
  · exact Tests.SubwordDecoder.native_constraints ⟨2,by decide⟩
  · exact Tests.SubwordDecoder.native_constraints ⟨3,by decide⟩
  · exact Tests.SubwordDecoder.native_constraints ⟨4,by decide⟩
  · exact Tests.SubwordDecoder.native_constraints ⟨5,by decide⟩
  · exact Tests.SubwordDecoder.native_constraints ⟨6,by decide⟩
  · exact alias_constraints

end Tests.SubwordHistoryRows
