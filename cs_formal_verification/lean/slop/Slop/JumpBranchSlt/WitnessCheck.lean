module
public import Slop.WitnessCheck
public import Human.Circuits.JumpBranchSlt.Artifact
public import Slop.CleanCore.Circuit.Operations
public import Slop.Constraints

@[expose] public section

/-! Comparison/branch/jump witness tests by evaluation (`Slop/WitnessCheck.lean`): the checked tables of the
    imported lookups. -/

namespace Airbender.JumpBranchSlt
open Verification
variable {p : Nat} [Fact p.Prime]

/-- The tables the imported lookups query, in order: four range checks, then the register-is-zero, sign,
    conditional and jump-cleanup tables. -/
def checkedTables : List (CheckedTable (ZMod p)) :=
  List.replicate 4 range16Checked ++
    [staticRowChecked regIsZeroTable rfl fun (_, _) => rfl, staticRowChecked u16SignTable rfl fun (_, _) => rfl,
      staticRowChecked conditionalTable rfl fun (_, _) => rfl,
      staticRowChecked jumpCleanupTable rfl fun (_, _, _) => rfl]

theorem lookup_tables :
    (FlatOperation.lookups (importedConstraints (p := p))).map Lookup.table = checkedTables.map CheckedTable.table := by
  rfl

theorem timestamp_tables :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).map Lookup.table =
      (List.replicate 8 timestampChecked).map CheckedTable.table := by
  rfl

/-- The row's constraints and clock lookups hold if both checks evaluate to `true`. -/
theorem holds_of_check {w : Nat → ZMod p} (check : checkOps w importedConstraints checkedTables = true)
    (timestamps : checkOps w importedConstraintsTimestampLookups (List.replicate 8 timestampChecked) = true) :
    FlatOperation.ConstraintsHoldFlat (environment w) clockConstraints :=
  holds_append (holds_of_checkOps lookup_tables check) (holds_of_checkOps timestamp_tables timestamps)

end Airbender.JumpBranchSlt
