module
public import Proven.Setup.Native.BlakeG.Columns

@[expose] public section

namespace Airbender.Blake2G.Control
open Import.Setup SetupProofs

/-- Each column of the imported setup is the column formula (kernel scans), and the column formula is the reviewed
    row formula. -/
theorem setup_import : SetupImportClaim := by
  refine ⟨rfl, rfl, fun index bound position => ?_⟩
  change decode _ index = (paddedRow index)[position]
  replace bound : index < 4194304 := bound
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := column_eq index
  fin_cases position
  · exact (column0_rows index bound).trans c0.symm
  · exact (column1_rows index bound).trans c1.symm
  · exact (column2_rows index bound).trans c2.symm
  · exact (column3_rows index bound).trans c3.symm
  · exact (column4_rows index bound).trans c4.symm
  · exact (column5_rows index bound).trans c5.symm
  · exact (column6_rows index bound).trans c6.symm
  · exact (column7_rows index bound).trans c7.symm
  · exact (column8_rows index bound).trans c8.symm

end Airbender.Blake2G.Control
