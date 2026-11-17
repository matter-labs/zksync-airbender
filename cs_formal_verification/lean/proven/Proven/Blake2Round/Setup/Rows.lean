module
public import Proven.Setup.Native.BlakeRound.Columns
public import Mathlib.Tactic.IntervalCases
public import Human.Circuits.Blake2Round.Tables.Setup

@[expose] public section

/- Row meaning of the imported setup: every column decodes to its row formula on all 2^20 exported rows. The kernel
   scans of `Proven.Setup.Native.BlakeRound` check each column against its fast formula, and `columns_eq` makes the
   fast formulas equal to `spec0` to `spec5`. -/

namespace Airbender.Blake2Round.SetupProofs
open Airbender.Import.Setup

set_option warningAsError true

theorem col0_rows : ∀ n < 1048576, decode blake2RoundSetup_col0 n = col0Spec n := fun n bound => by
  rw [column0_rows n bound, (columns_eq n).1]; rfl

theorem col1_rows : ∀ n < 1048576, decode blake2RoundSetup_col1 n = col1Spec n := fun n bound => by
  rw [column1_rows n bound, (columns_eq n).2.1]; rfl

theorem col2_rows : ∀ n < 1048576, decode blake2RoundSetup_col2 n = col2Spec n := fun n bound => by
  rw [column2_rows n bound, (columns_eq n).2.2.1]; rfl

theorem col3_rows : ∀ n < 1048576, decode blake2RoundSetup_col3 n = col3Spec n := fun n bound => by
  rw [column3_rows n bound, (columns_eq n).2.2.2.1]; rfl

theorem col4_rows : ∀ n < 1048576, decode blake2RoundSetup_col4 n = col4Spec n := fun n bound => by
  rw [column4_rows n bound, (columns_eq n).2.2.2.2.1]; rfl

theorem col5_rows : ∀ n < 1048576, decode blake2RoundSetup_col5 n = col5Spec n := fun n bound => by
  rw [column5_rows n bound, (columns_eq n).2.2.2.2.2]; rfl

/-- The row formulas, one per column. -/
def formulaRow (n : Nat) : Vector Nat 6 := #v[spec0 n, spec1 n, spec2 n, spec3 n, spec4 n, spec5 n]

theorem traceLen_eq : blake2RoundSetup.traceLen = 1048576 := by rfl

/-- Every exported row is the formula row. -/
theorem setupRow_eq (n : Nat) (hn : n < 1048576) :
    setupRow n = (formulaRow n).map Int.ofNat := by
  ext c hc
  simp only [setupRow, Vector.getElem_ofFn, Vector.getElem_map, formulaRow]
  interval_cases c
  · exact col0_rows n hn
  · exact col1_rows n hn
  · exact col2_rows n hn
  · exact col3_rows n hn
  · exact col4_rows n hn
  · exact col5_rows n hn

end Airbender.Blake2Round.SetupProofs
