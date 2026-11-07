import Slop.KeccakSplit.Setup.ColumnParity.ShapesOk
import Slop.KeccakSplit.Setup.ColumnParity.Formula
import Human.Circuits.KeccakSplit.Tables.Setup
import Mathlib.Tactic.IntervalCases

/- Row meaning of the imported setup: every column decodes to its row formula on all 2^22
   exported rows. Each column is a few blocks: grid blocks and long affine runs matched by
   shape (`Shapes`, proved in `ShapesOk`), the controller rows checked row by row (`scan`). -/

namespace Airbender.Keccak.Split.ColumnParity.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option warningAsError true

theorem col0_rows : ∀ n < 4194304, decode columnParitySetup_col0 n = col0Spec n :=
  rows_of_scan _ col0_longs (by decide +kernel) (by decide +kernel)

theorem col1_rows : ∀ n < 4194304, decode columnParitySetup_col1 n = col1Spec n :=
  rows_of_scan _ col1_longs (by decide +kernel) (by decide +kernel)

theorem col2_rows : ∀ n < 4194304, decode columnParitySetup_col2 n = col2Spec n :=
  rows_of_scan _ col2_longs (by decide +kernel) (by decide +kernel)

theorem col3_rows : ∀ n < 4194304, decode columnParitySetup_col3 n = col3Spec n :=
  rows_of_scan _ col3_longs (by decide +kernel) (by decide +kernel)

theorem col4_rows : ∀ n < 4194304, decode columnParitySetup_col4 n = col4Spec n :=
  rows_of_scan _ col4_longs (by decide +kernel) (by decide +kernel)

theorem col5_rows : ∀ n < 4194304, decode columnParitySetup_col5 n = col5Spec n :=
  rows_of_scan _ col5_longs (by decide +kernel) (by decide +kernel)

theorem col6_rows : ∀ n < 4194304, decode columnParitySetup_col6 n = col6Spec n :=
  rows_of_scan _ col6_longs (by decide +kernel) (by decide +kernel)

theorem col7_rows : ∀ n < 4194304, decode columnParitySetup_col7 n = col7Spec n :=
  rows_of_scan _ col7_longs (by decide +kernel) (by decide +kernel)

theorem traceLen_eq : columnParitySetup.traceLen = 4194304 := rfl

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
