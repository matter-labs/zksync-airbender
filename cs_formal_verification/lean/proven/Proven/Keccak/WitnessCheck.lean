module
public import Proven.WitnessCheck
public import Human.Circuits.Keccak.Tables.Setup
public import Human.Circuits.Keccak.Tables.Controller
public import Proven.CleanCore.Circuit.Operations

@[expose] public section

/-! Keccak special5 witness tests by evaluation (`Proven/WitnessCheck.lean`): the checked tables of the imported
    lookups, over the modeled setup with the modeled controller rows (`Controller.rows`). -/

namespace Airbender.Keccak
open Verification
variable {p : Nat} [Fact p.Prime]

/-- The modeled setup table, checked by its `index` (rows in list form). -/
def setupChecked : CheckedTable (ZMod p) :=
  staticChecked (setupTable Controller.rows) rfl
    (fun i => (setupRow Controller.rows i).toList.map (fun n : Nat => (n : ZMod p)))
    (fun _ => Vector.toList_map)

/-- The tables the imported lookups query, in order: one timestamp check, 41 setup queries. -/
def checkedTables : List (CheckedTable (ZMod p)) :=
  timestampChecked :: List.replicate 41 setupChecked

theorem lookup_tables :
    (FlatOperation.lookups (importedConstraints (p := p) (setupTable Controller.rows))).map Lookup.table =
      checkedTables.map CheckedTable.table := by
  rfl

theorem holds_of_check {w : Nat → ZMod p}
    (check : checkOps w (importedConstraints (setupTable Controller.rows)) checkedTables = true) :
    FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints (setupTable Controller.rows)) :=
  holds_of_checkOps lookup_tables check

theorem timestamp_tables :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).map Lookup.table =
      (List.replicate 30 timestampChecked).map CheckedTable.table := by
  rfl

theorem timestamps_of_check {w : Nat → ZMod p}
    (check : checkOps w importedConstraintsTimestampLookups (List.replicate 30 timestampChecked) = true) :
    FlatOperation.ConstraintsHoldFlat (environment w) importedConstraintsTimestampLookups :=
  holds_of_checkOps timestamp_tables check

end Airbender.Keccak
