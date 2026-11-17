module
public import Proven.Setup.Native.KeccakColumnParity.Columns
public import Proven.KeccakSplit.Setup.ColumnParity.Formula
public import Human.Circuits.KeccakSplit.Tables.Setup
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/- Row meaning of the imported setup: every column decodes to its row formula on all 2^22 exported rows. The kernel
   scans of `Proven.Setup.Native.KeccakColumnParity` check each column against its fast formula, and `columns_eq`
   makes the fast formulas equal to `spec0` to `spec7`. -/

namespace Airbender.Keccak.Split.ColumnParity.SetupProofs
open Airbender.Import.Setup

set_option warningAsError true

theorem col0_rows : ∀ n < 4194304, decode columnParitySetup_col0 n = Int.ofNat (spec0 n) := fun n bound => by
  rw [column0_rows n bound, (columns_eq n).1]; rfl

theorem col1_rows : ∀ n < 4194304, decode columnParitySetup_col1 n = Int.ofNat (spec1 n) := fun n bound => by
  rw [column1_rows n bound, (columns_eq n).2.1]; rfl

theorem col2_rows : ∀ n < 4194304, decode columnParitySetup_col2 n = Int.ofNat (spec2 n) := fun n bound => by
  rw [column2_rows n bound, (columns_eq n).2.2.1]; rfl

theorem col3_rows : ∀ n < 4194304, decode columnParitySetup_col3 n = Int.ofNat (spec3 n) := fun n bound => by
  rw [column3_rows n bound, (columns_eq n).2.2.2.1]; rfl

theorem col4_rows : ∀ n < 4194304, decode columnParitySetup_col4 n = Int.ofNat (spec4 n) := fun n bound => by
  rw [column4_rows n bound, (columns_eq n).2.2.2.2.1]; rfl

theorem col5_rows : ∀ n < 4194304, decode columnParitySetup_col5 n = Int.ofNat (spec5 n) := fun n bound => by
  rw [column5_rows n bound, (columns_eq n).2.2.2.2.2.1]; rfl

theorem col6_rows : ∀ n < 4194304, decode columnParitySetup_col6 n = Int.ofNat (spec6 n) := fun n bound => by
  rw [column6_rows n bound, (columns_eq n).2.2.2.2.2.2.1]; rfl

theorem col7_rows : ∀ n < 4194304, decode columnParitySetup_col7 n = Int.ofNat (spec7 n) := fun n bound => by
  rw [column7_rows n bound, (columns_eq n).2.2.2.2.2.2.2]; rfl

theorem traceLen_eq : columnParitySetup.traceLen = 4194304 := by rfl

/-- Every exported row is the formula row. -/
theorem setupRow_eq (n : Nat) (hn : n < 4194304) :
    Airbender.Keccak.Split.setupRow columnParitySetup 8 n = (formulaRow n).map Int.ofNat := by
  ext c hc
  simp only [Airbender.Keccak.Split.setupRow, Vector.getElem_ofFn, Vector.getElem_map, formulaRow]
  interval_cases c
  · exact col0_rows n hn
  · exact col1_rows n hn
  · exact col2_rows n hn
  · exact col3_rows n hn
  · exact col4_rows n hn
  · exact col5_rows n hn
  · exact col6_rows n hn
  · exact col7_rows n hn

end Airbender.Keccak.Split.ColumnParity.SetupProofs
