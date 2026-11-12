module
public import Slop.WitnessCheck
public import Human.Circuits.SubwordMemory.Artifact
public import Human.Helpers.Tables.Subword
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

/-! Subword-memory witness tests by evaluation (`Slop/WitnessCheck.lean`): the checked tables of the imported
lookups. -/

namespace Airbender.SubwordMemory
open Verification
variable {p : Nat} [Fact p.Prime]

/-- The subword table over a program image, checked by its `index`. -/
def subwordChecked (program : Nat → BitVec 32) : CheckedTable (ZMod p) :=
  staticChecked (subwordTable program) rfl (fun i => (subwordRow program i).toList.map (fun n : Nat => (n : ZMod p)))
    (fun _ => Vector.toList_map)

/-- The tables the imported lookups query, in order: five range checks, then two queries of `setup`. -/
def checkedTables (setup : CheckedTable (ZMod p)) : List (CheckedTable (ZMod p)) :=
  List.replicate 5 range16Checked ++ List.replicate 2 setup

theorem lookup_tables {table : Table (ZMod p) (fields 9)} {setup : CheckedTable (ZMod p)}
    (queried : setup.table = table.toRaw) :
    (FlatOperation.lookups (importedConstraints table)).map Lookup.table =
      (checkedTables setup).map CheckedTable.table := by
  simp only [checkedTables, List.map_append, List.map_replicate, queried]
  rfl

theorem holds_of_check {table : Table (ZMod p) (fields 9)} {w : Nat → ZMod p} (setup : CheckedTable (ZMod p))
    (queried : setup.table = table.toRaw) (check : checkOps w (importedConstraints table) (checkedTables setup) = true) :
    FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints table) :=
  holds_of_checkOps (lookup_tables queried) check

theorem timestamp_tables :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).map Lookup.table =
      (List.replicate 8 timestampChecked).map CheckedTable.table := by
  rfl

theorem timestamps_of_check {w : Nat → ZMod p}
    (check : checkOps w importedConstraintsTimestampLookups (List.replicate 8 timestampChecked) = true) :
    FlatOperation.ConstraintsHoldFlat (environment w) importedConstraintsTimestampLookups :=
  holds_of_checkOps timestamp_tables check

end Airbender.SubwordMemory
