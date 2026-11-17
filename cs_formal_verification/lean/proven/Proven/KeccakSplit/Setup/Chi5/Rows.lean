module
public import Proven.Setup.Native.KeccakChi5.Columns
public import Proven.KeccakSplit.Setup.Chi5.Formula
public import Human.Circuits.KeccakSplit.Tables.Setup
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/- Row meaning of the imported setup: every column decodes to its row formula on all 2^22 exported rows. The kernel
   scans of `Proven.Setup.Native.KeccakChi5` check each column against its fast formula, and `columns_eq`
   makes the fast formulas equal to `spec0` to `spec10`. -/

namespace Airbender.Keccak.Split.Chi5.SetupProofs
open Airbender.Import.Setup

set_option warningAsError true

theorem col0_rows : ∀ n < 4194304, decode chi5Setup_col0 n = Int.ofNat (spec0 n) := fun n bound => by
  rw [column0_rows n bound, (columns_eq n).1]; rfl

theorem col1_rows : ∀ n < 4194304, decode chi5Setup_col1 n = Int.ofNat (spec1 n) := fun n bound => by
  rw [column1_rows n bound, (columns_eq n).2.1]; rfl

theorem col2_rows : ∀ n < 4194304, decode chi5Setup_col2 n = Int.ofNat (spec2 n) := fun n bound => by
  rw [column2_rows n bound, (columns_eq n).2.2.1]; rfl

theorem col3_rows : ∀ n < 4194304, decode chi5Setup_col3 n = Int.ofNat (spec3 n) := fun n bound => by
  rw [column3_rows n bound, (columns_eq n).2.2.2.1]; rfl

theorem col4_rows : ∀ n < 4194304, decode chi5Setup_col4 n = Int.ofNat (spec4 n) := fun n bound => by
  rw [column4_rows n bound, (columns_eq n).2.2.2.2.1]; rfl

theorem col5_rows : ∀ n < 4194304, decode chi5Setup_col5 n = Int.ofNat (spec5 n) := fun n bound => by
  rw [column5_rows n bound, (columns_eq n).2.2.2.2.2.1]; rfl

theorem col6_rows : ∀ n < 4194304, decode chi5Setup_col6 n = Int.ofNat (spec6 n) := fun n bound => by
  rw [column6_rows n bound, (columns_eq n).2.2.2.2.2.2.1]; rfl

theorem col7_rows : ∀ n < 4194304, decode chi5Setup_col7 n = Int.ofNat (spec7 n) := fun n bound => by
  rw [column7_rows n bound, (columns_eq n).2.2.2.2.2.2.2.1]; rfl

theorem col8_rows : ∀ n < 4194304, decode chi5Setup_col8 n = Int.ofNat (spec8 n) := fun n bound => by
  rw [column8_rows n bound, (columns_eq n).2.2.2.2.2.2.2.2.1]; rfl

theorem col9_rows : ∀ n < 4194304, decode chi5Setup_col9 n = Int.ofNat (spec9 n) := fun n bound => by
  rw [column9_rows n bound, (columns_eq n).2.2.2.2.2.2.2.2.2.1]; rfl

theorem col10_rows : ∀ n < 4194304, decode chi5Setup_col10 n = Int.ofNat (spec10 n) := fun n bound => by
  rw [column10_rows n bound, (columns_eq n).2.2.2.2.2.2.2.2.2.2]; rfl

theorem traceLen_eq : chi5Setup.traceLen = 4194304 := by rfl

/-- Every exported row is the formula row. -/
theorem setupRow_eq (n : Nat) (hn : n < 4194304) :
    Airbender.Keccak.Split.setupRow chi5Setup 11 n = (formulaRow n).map Int.ofNat := by
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
  · exact col8_rows n hn
  · exact col9_rows n hn
  · exact col10_rows n hn

end Airbender.Keccak.Split.Chi5.SetupProofs
