import Airbender.Proofs.MulDiv.ArtifactChecks
import Airbender.Proofs.MulDiv.SmallRange
import Airbender.Proofs.Constraints
import Airbender.Review.Helpers.Properties

namespace Airbender.MulDiv.Proofs
open Verification

/-- Every declared native byte range comes from the six retained fixed queries.
    This extracts actual constraints; no byte bounds are supplied by a caller. -/
theorem native_byte_bounds {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints) :
    ∀ column ∈ [35,36,37,38,39,40,41,42,44,47,49], (w column).val < 256 := by
  have query0 : smallRangeTable.Contains #[] #v[w 35, w 36, 0] := by
    have query := lookup_of_holds holds ⟨14, by rw [lookup_count]; decide⟩
    simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, fixed3,
      Table.toRaw, smallRangeTable, Table.fromStatic, StaticTable.toTable,
      Expression.eval, environment, ProvableType.fromElements] using query
  have bounds0 := small_range_values query0
  have query1 : smallRangeTable.Contains #[] #v[w 37, w 38, 0] := by
    have query := lookup_of_holds holds ⟨15, by rw [lookup_count]; decide⟩
    simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, fixed3,
      Table.toRaw, smallRangeTable, Table.fromStatic, StaticTable.toTable,
      Expression.eval, environment, ProvableType.fromElements] using query
  have bounds1 := small_range_values query1
  have query2 : smallRangeTable.Contains #[] #v[w 39, w 40, 0] := by
    have query := lookup_of_holds holds ⟨16, by rw [lookup_count]; decide⟩
    simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, fixed3,
      Table.toRaw, smallRangeTable, Table.fromStatic, StaticTable.toTable,
      Expression.eval, environment, ProvableType.fromElements] using query
  have bounds2 := small_range_values query2
  have query3 : smallRangeTable.Contains #[] #v[w 41, w 42, 0] := by
    have query := lookup_of_holds holds ⟨17, by rw [lookup_count]; decide⟩
    simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, fixed3,
      Table.toRaw, smallRangeTable, Table.fromStatic, StaticTable.toTable,
      Expression.eval, environment, ProvableType.fromElements] using query
  have bounds3 := small_range_values query3
  have query4 : smallRangeTable.Contains #[] #v[w 44, w 47, 0] := by
    have query := lookup_of_holds holds ⟨18, by rw [lookup_count]; decide⟩
    simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, fixed3,
      Table.toRaw, smallRangeTable, Table.fromStatic, StaticTable.toTable,
      Expression.eval, environment, ProvableType.fromElements] using query
  have bounds4 := small_range_values query4
  have query5 : smallRangeTable.Contains #[] #v[w 49, 0, 0] := by
    have query := lookup_of_holds holds ⟨19, by rw [lookup_count]; decide⟩
    simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, fixed3,
      Table.toRaw, smallRangeTable, Table.fromStatic, StaticTable.toTable,
      Expression.eval, environment, ProvableType.fromElements] using query
  have bounds5 := small_range_values query5
  intro column member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bounds0.1
  · exact bounds0.2.1
  · exact bounds1.1
  · exact bounds1.2.1
  · exact bounds2.1
  · exact bounds2.2.1
  · exact bounds3.1
  · exact bounds3.2.1
  · exact bounds4.1
  · exact bounds4.2.1
  · exact bounds5.1

end Airbender.MulDiv.Proofs
