module
public import Slop.WitnessCheck
public import Human.Circuits.ShiftBinop.Artifact
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

/-! Shift/binop witness tests by evaluation (`Slop/WitnessCheck.lean`): the checked tables of the imported lookups. -/

namespace Airbender.ShiftBinop
open Verification
variable {p : Nat} [Fact p.Prime]

/-- The shift/binop table, checked by its `index`. -/
def shiftBinopChecked : CheckedTable (ZMod p) :=
  staticChecked shiftBinopTable rfl (fun i => (shiftBinopRow i).toList.map (fun n : Nat => (n : ZMod p)))
    (fun _ => Vector.toList_map)

/-- The tables the imported lookups query, in order (two 16-bit ranges, five shift/binop queries), then the eight
    timestamp queries. -/
def checkedTables : List (CheckedTable (ZMod p)) :=
  List.replicate 2 range16Checked ++ List.replicate 5 shiftBinopChecked ++ List.replicate 8 timestampChecked

theorem holds_of_check {w : Nat → ZMod p} (check : checkOps w clockConstraints checkedTables = true) :
    FlatOperation.ConstraintsHoldFlat (environment w) clockConstraints :=
  holds_of_checkOps rfl check

end Airbender.ShiftBinop
