module
public import Slop.WitnessCheck
public import Human.Circuits.Bigint.Artifact
public import Human.Circuits.Bigint.Tables.Setup
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

/-! Bigint witness tests by evaluation (`Slop/WitnessCheck.lean`): the checked tables of the imported lookups. -/

namespace Airbender.Bigint
open Verification
variable {p : Nat} [Fact p.Prime]

/-- The fixed setup table, checked by its `index`. -/
def setupChecked : CheckedTable (ZMod p) := staticChecked setupTable rfl

/-- The tables the imported lookups query, in order: 32 range checks, two timestamp checks, 61 setup queries. -/
def checkedTables : List (CheckedTable (ZMod p)) :=
  List.replicate 32 range16Checked ++ List.replicate 2 timestampChecked ++ List.replicate 61 setupChecked

theorem lookup_tables :
    (FlatOperation.lookups (importedConstraints (p := p) setupTable)).map Lookup.table =
      checkedTables.map CheckedTable.table := by
  rfl

theorem holds_of_check {w : Nat → ZMod p} (check : checkOps w (importedConstraints setupTable) checkedTables = true) :
    FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setupTable) :=
  holds_of_checkOps lookup_tables check

theorem timestamp_tables :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).map Lookup.table =
      (List.replicate 41 timestampChecked).map CheckedTable.table := by
  rfl

theorem timestamps_of_check {w : Nat → ZMod p}
    (check : checkOps w importedConstraintsTimestampLookups (List.replicate 41 timestampChecked) = true) :
    FlatOperation.ConstraintsHoldFlat (environment w) importedConstraintsTimestampLookups :=
  holds_of_checkOps timestamp_tables check

end Airbender.Bigint
