import Airbender.Proofs.SubwordMemory.ArtifactChecks
import Airbender.Proofs.Constraints
import Airbender.Review.Helpers.Properties
import Mathlib.Tactic.FinCases

namespace Airbender.SubwordMemory.Proofs
open Verification
set_option autoImplicit false

/-- Both multiplexed slots retain all three fields and their witness selectors. -/
theorem native_queries {p : Nat} [Fact p.Prime] {rom : WordROM} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (slot : Fin 2) :
    (NativeSubwordLookup.table rom).Contains #[]
      #v[w (52 + 4 * slot.val),w (53 + 4 * slot.val),
         w (54 + 4 * slot.val),w (55 + 4 * slot.val)] := by
  fin_cases slot
  · have query := lookup_of_holds holds ⟨12, by rw [lookup_count]; decide⟩
    simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, NativeSubwordLookup.lookup,
      Table.toRaw, NativeSubwordLookup.table, Table.fromStatic, StaticTable.toTable,
      Expression.eval, environment, ProvableType.fromElements] using query
  · have query := lookup_of_holds holds ⟨13, by rw [lookup_count]; decide⟩
    simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, NativeSubwordLookup.lookup,
      Table.toRaw, NativeSubwordLookup.table, Table.fromStatic, StaticTable.toTable,
      Expression.eval, environment, ProvableType.fromElements] using query

end Airbender.SubwordMemory.Proofs
