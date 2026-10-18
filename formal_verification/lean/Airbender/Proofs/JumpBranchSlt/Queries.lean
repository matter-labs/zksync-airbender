import Airbender.Review.Circuits.JumpBranchSlt.Model
import Airbender.Proofs.JumpBranchSlt.ArtifactChecks
import Airbender.Proofs.JumpBranchSlt.ControlTables
import Airbender.Proofs.Constraints
import Airbender.Review.Helpers.Properties

namespace Airbender.JumpBranchSlt.Proofs
open Verification

theorem conditional_query {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints) :
    conditionalControlTable.Contains #[] #v[controlBits w, w 11, w 35] := by
  have query := lookup_of_holds holds ⟨14, by rw [lookup_count]; decide⟩
  simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, fixed3,
    Table.toRaw, conditionalControlTable, Table.fromStatic, StaticTable.toTable,
    Expression.eval, environment, ProvableType.fromElements, controlBits] using query

theorem cleanup_query {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints) :
    jumpCleanupTable.Contains #[] #v[w 42, w 47, w 48] := by
  have query := lookup_of_holds holds ⟨15, by rw [lookup_count]; decide⟩
  simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, fixed3,
    Table.toRaw, jumpCleanupTable, Table.fromStatic, StaticTable.toTable,
    Expression.eval, environment, ProvableType.fromElements] using query

theorem fixed_effects {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints) : FixedEffects w := by
  obtain ⟨bits, tag, flag⟩ := conditional_values (conditional_query holds)
  obtain ⟨key, bit, cleaned⟩ := cleanup_values (cleanup_query holds)
  exact ⟨bits, tag, flag, key, bit, cleaned⟩

end Airbender.JumpBranchSlt.Proofs
