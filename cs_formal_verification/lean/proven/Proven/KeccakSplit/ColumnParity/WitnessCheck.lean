module
public import Proven.WitnessCheck
public import Proven.KeccakSplit.Setup.ColumnParity.Rows
public import Human.Circuits.KeccakSplit.ColumnParity.Artifact
public import Proven.CleanCore.Circuit.Operations

@[expose] public section

/-! Column-parity witness tests by evaluation (`Proven/WitnessCheck.lean`), over BabyBear: the checked tables of the
    imported lookups. The exported setup is checked against its row formulas (`SetupProofs.setupRow_eq`) at a
    given list of row numbers, so the kernel evaluates formulas instead of decoding the exported blocks. -/

namespace Airbender.Keccak.Split.ColumnParity
open Verification _root_.Airbender.Keccak.Split.ColumnParity.SetupProofs

/-- A field row whose entries are formula row `n`'s is that row of the exported setup. -/
theorem formula_row {row : Vector (ZMod babyBearModulus) 8} {n : Nat} (bound : n < 4194304)
    (listed : (formulaRow n).toList.map (fun v : Nat => (v : ZMod babyBearModulus)) = row.toList) :
    row = (Split.setupRow columnParitySetup 8 n).map (fun v : Int => (v : ZMod babyBearModulus)) := by
  rw [setupRow_eq n bound, Vector.map_map]
  apply Vector.toList_inj.mp
  rw [← listed, Vector.toList_map]
  simp only [Function.comp_def, Int.ofNat_eq_natCast, Int.cast_natCast]

/-- The exported setup table, checked against the formula rows numbered `rows`. -/
noncomputable def setupChecked (rows : List Nat) : CheckedTable (ZMod babyBearModulus) where
  table := (setup (p := babyBearModulus)).toRaw
  check xs := rows.any fun n => decide (n < 4194304) &&
    listEq ((formulaRow n).toList.map (fun v : Nat => (v : ZMod babyBearModulus))) xs
  sound row h := by
    obtain ⟨n, -, h⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨⟨n, by change n < columnParitySetup.traceLen; rw [traceLen_eq]; exact h.1⟩,
      formula_row h.1 (eq_of_listEq h.2)⟩

/-- The tables the imported lookups query, in order: one timestamp check, 22 setup queries. -/
noncomputable def checkedTables (rows : List Nat) : List (CheckedTable (ZMod babyBearModulus)) :=
  timestampChecked :: List.replicate 22 (setupChecked rows)

theorem lookup_tables (rows : List Nat) :
    (FlatOperation.lookups (importedConstraints (p := babyBearModulus) setup)).map Lookup.table =
      (checkedTables rows).map CheckedTable.table := by
  rfl

theorem holds_of_check {w : Nat → ZMod babyBearModulus} (rows : List Nat)
    (check : checkOps w (importedConstraints setup) (checkedTables rows) = true) :
    FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup) :=
  holds_of_checkOps (lookup_tables rows) check

theorem timestamp_tables :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := babyBearModulus))).map Lookup.table =
      (List.replicate 30 timestampChecked).map CheckedTable.table := by
  rfl

theorem timestamps_of_check {w : Nat → ZMod babyBearModulus}
    (check : checkOps w importedConstraintsTimestampLookups (List.replicate 30 timestampChecked) = true) :
    FlatOperation.ConstraintsHoldFlat (environment w) importedConstraintsTimestampLookups :=
  holds_of_checkOps timestamp_tables check

end Airbender.Keccak.Split.ColumnParity
