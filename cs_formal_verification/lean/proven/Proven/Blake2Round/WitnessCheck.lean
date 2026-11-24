module
public import Proven.WitnessCheck
public import Proven.Blake2Round.Setup.Rows
public import Human.Circuits.Blake2Round.Artifact
public import Proven.CleanCore.Circuit.Operations

@[expose] public section

/-! Extended-control Blake2s round witness tests by evaluation (`Proven/WitnessCheck.lean`): the checked tables of
    the imported lookups. The exported setup is checked by its `index` against its row formulas
    (`SetupProofs.setupRow_eq`), so the kernel evaluates formulas instead of decoding the exported blocks. -/

namespace Airbender.Blake2Round
open Verification
variable {p : Nat} [Fact p.Prime]

/-- The exported setup table, checked by its `index`, rows by formula. -/
noncomputable def setupChecked : CheckedTable (ZMod p) :=
  staticChecked setupTable rfl
    (fun i => (SetupProofs.formulaRow i.val).toList.map (fun n : Nat => (n : ZMod p)))
    (fun i => by
      have bound : i.val < 1048576 :=
        lt_of_lt_of_eq (i.isLt : i.val < blake2RoundSetup.traceLen) SetupProofs.traceLen_eq
      change ((setupRow i.val).map (fun v : Int => (v : ZMod p))).toList = _
      rw [SetupProofs.setupRow_eq i.val bound, Vector.map_map, Vector.toList_map]
      simp only [Function.comp_def, Int.ofNat_eq_natCast, Int.cast_natCast])

/-- The tables the imported lookups query, in order: two timestamp checks, 192 setup queries. -/
noncomputable def checkedTables : List (CheckedTable (ZMod p)) :=
  List.replicate 2 timestampChecked ++ List.replicate 192 setupChecked

theorem lookup_tables :
    (FlatOperation.lookups (importedConstraints (p := p) setupTable)).map Lookup.table =
      checkedTables.map CheckedTable.table := by
  rfl

theorem holds_of_check {w : Nat → ZMod p} (check : checkOps w (importedConstraints setupTable) checkedTables = true) :
    FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setupTable) :=
  holds_of_checkOps lookup_tables check

theorem timestamp_tables :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).map Lookup.table =
      (List.replicate 89 timestampChecked).map CheckedTable.table := by
  rfl

theorem timestamps_of_check {w : Nat → ZMod p}
    (check : checkOps w importedConstraintsTimestampLookups (List.replicate 89 timestampChecked) = true) :
    FlatOperation.ConstraintsHoldFlat (environment w) importedConstraintsTimestampLookups :=
  holds_of_checkOps timestamp_tables check

end Airbender.Blake2Round
