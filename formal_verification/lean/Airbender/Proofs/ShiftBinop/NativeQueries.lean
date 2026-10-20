import Airbender.Review.Circuits.ShiftBinop.Artifact
import Airbender.Proofs.ShiftBinop.NativeRegions
import Airbender.Proofs.Constraints
import Airbender.Review.Helpers.Properties
import Mathlib.Tactic.FinCases

namespace Airbender.ShiftBinop.NativeLookupProofs
open Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Extract all four actual dynamic queries from original Clean acceptance. -/
theorem native_queries {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (slot : Fin 4) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[]
      #v[w (39 + 4 * slot.val), w (40 + 4 * slot.val),
         w (41 + 4 * slot.val), w (42 + 4 * slot.val)] := by
  fin_cases slot
  · have query := lookup_of_holds holds ⟨8, by change 8 < 12; decide⟩
    simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, NativeShiftLookup.lookup,
      Table.toRaw, NativeShiftLookup.table, Table.fromStatic, StaticTable.toTable,
      Expression.eval, environment, ProvableType.fromElements] using query
  · have query := lookup_of_holds holds ⟨9, by change 9 < 12; decide⟩
    simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, NativeShiftLookup.lookup,
      Table.toRaw, NativeShiftLookup.table, Table.fromStatic, StaticTable.toTable,
      Expression.eval, environment, ProvableType.fromElements] using query
  · have query := lookup_of_holds holds ⟨10, by change 10 < 12; decide⟩
    simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, NativeShiftLookup.lookup,
      Table.toRaw, NativeShiftLookup.table, Table.fromStatic, StaticTable.toTable,
      Expression.eval, environment, ProvableType.fromElements] using query
  · have query := lookup_of_holds holds ⟨11, by change 11 < 12; decide⟩
    simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, NativeShiftLookup.lookup,
      Table.toRaw, NativeShiftLookup.table, Table.fromStatic, StaticTable.toTable,
      Expression.eval, environment, ProvableType.fromElements] using query

/-- Selector bounds come from accepted native rows, rather than caller-supplied bounds. -/
theorem native_selectors {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (slot : Fin 4) :
    (w (42 + 4 * slot.val)).val ∈ [0, 4, 6, 7, 25, 47, 48, 49, 50, 51, 52, 53] := by
  have selected := accepted_selector _ (native_queries holds slot)
  simpa using selected

end Airbender.ShiftBinop.NativeLookupProofs
