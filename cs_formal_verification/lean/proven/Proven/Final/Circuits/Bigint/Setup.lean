module
public import Proven.Setup.Native.Bigint.Columns

@[expose] public section

namespace Airbender.Bigint
open Import.Setup SetupProofs

/-- Each column of the imported setup is the column formula (kernel scans), and the column formula is the reviewed
    row formula. -/
theorem setup_import : SetupImportClaim := by
  refine ⟨rfl, rfl, fun index bound position => ?_⟩
  change decode _ index = (paddedRow index)[position]
  replace bound : index < 4194304 := bound
  obtain ⟨first, second, tag⟩ := columns_eq index
  fin_cases position
  · exact (column0_rows index bound).trans first.symm
  · exact (column1_rows index bound).trans second.symm
  · exact (column2_rows index bound).trans tag.symm

end Airbender.Bigint
