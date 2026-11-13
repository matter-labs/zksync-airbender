module
public import Proven.KeccakSplit.Setup.Chi5.ShapesOk
public import Proven.KeccakSplit.Setup.Chi5.Formula
public import Human.Circuits.KeccakSplit.Tables.Setup
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/- Row meaning of the imported setup: every column decodes to its row formula on all 2^22
   exported rows. Each column is a few blocks: grid blocks and long affine runs matched by
   shape (`Shapes`, proved in `ShapesOk`), the controller rows checked row by row (`scan`). -/

namespace Airbender.Keccak.Split.Chi5.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option warningAsError true

theorem col0_rows : ∀ n < 4194304, decode chi5Setup_col0 n = col0Spec n :=
  rows_of_scan _ col0_longs (by decide +kernel) (by decide +kernel)

theorem col1_rows : ∀ n < 4194304, decode chi5Setup_col1 n = col1Spec n :=
  rows_of_scan _ col1_longs (by decide +kernel) (by decide +kernel)

theorem col2_rows : ∀ n < 4194304, decode chi5Setup_col2 n = col2Spec n :=
  rows_of_scan _ col2_longs (by decide +kernel) (by decide +kernel)

theorem col3_rows : ∀ n < 4194304, decode chi5Setup_col3 n = col3Spec n :=
  rows_of_scan _ col3_longs (by decide +kernel) (by decide +kernel)

theorem col4_rows : ∀ n < 4194304, decode chi5Setup_col4 n = col4Spec n :=
  rows_of_scan _ col4_longs (by decide +kernel) (by decide +kernel)

theorem col5_rows : ∀ n < 4194304, decode chi5Setup_col5 n = col5Spec n :=
  rows_of_scan _ col5_longs (by decide +kernel) (by decide +kernel)

theorem col6_rows : ∀ n < 4194304, decode chi5Setup_col6 n = col6Spec n :=
  rows_of_scan _ col6_longs (by decide +kernel) (by decide +kernel)

theorem col7_rows : ∀ n < 4194304, decode chi5Setup_col7 n = col7Spec n :=
  rows_of_scan _ col7_longs (by decide +kernel) (by decide +kernel)

theorem col8_rows : ∀ n < 4194304, decode chi5Setup_col8 n = col8Spec n :=
  rows_of_scan _ col8_longs (by decide +kernel) (by decide +kernel)

theorem col9_rows : ∀ n < 4194304, decode chi5Setup_col9 n = col9Spec n :=
  rows_of_scan _ col9_longs (by decide +kernel) (by decide +kernel)

theorem col10_rows : ∀ n < 4194304, decode chi5Setup_col10 n = col10Spec n :=
  rows_of_scan _ col10_longs (by decide +kernel) (by decide +kernel)

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
