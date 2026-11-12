module
public import Slop.WitnessCheck
public import Human.Circuits.Blake2G.Artifact
public import Human.Circuits.Blake2G.Tables.Controller
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

/-! Blake2s G witness tests by evaluation (`Slop/WitnessCheck.lean`): the checked tables of the imported lookups,
    over the modeled setup (`Delegation.modeledSetup`'s G table). -/

namespace Airbender.Blake2G
open Verification
variable {p : Nat} [Fact p.Prime]

/-- The modeled setup table, checked by its `index` (rows in list form). -/
def setupChecked : CheckedTable (ZMod p) :=
  staticChecked (setupTable Control.controllerRows) rfl
    (fun i => (setupRow Control.controllerRows i).toList.map (fun n : Nat => (n : ZMod p)))
    (fun _ => Vector.toList_map)

/-- The tables the imported lookups query, in order: two timestamp checks, 19 setup queries. -/
def checkedTables : List (CheckedTable (ZMod p)) :=
  List.replicate 2 timestampChecked ++ List.replicate 19 setupChecked

theorem lookup_tables :
    (FlatOperation.lookups (importedConstraints (p := p) (setupTable Control.controllerRows))).map Lookup.table =
      checkedTables.map CheckedTable.table := by
  rfl

theorem holds_of_check {w : Nat → ZMod p}
    (check : checkOps w (importedConstraints (setupTable Control.controllerRows)) checkedTables = true) :
    FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints (setupTable Control.controllerRows)) :=
  holds_of_checkOps lookup_tables check

theorem timestamp_tables :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).map Lookup.table =
      (List.replicate 21 timestampChecked).map CheckedTable.table := by
  rfl

theorem timestamps_of_check {w : Nat → ZMod p}
    (check : checkOps w importedConstraintsTimestampLookups (List.replicate 21 timestampChecked) = true) :
    FlatOperation.ConstraintsHoldFlat (environment w) importedConstraintsTimestampLookups :=
  holds_of_checkOps timestamp_tables check

end Airbender.Blake2G
