module
public import Human.Circuits.KeccakSplit.Tables.SetupImport
public import Proven.KeccakSplit.Setup.ColumnParity.Rows

@[expose] public section

namespace Airbender.Keccak.Split.ColumnParity
open Import.Setup

/-- Each column of the imported column-parity setup is its row formula (kernel scans), on all 2^22 rows. -/
theorem setup_import : SetupImportClaim := by
  refine ⟨rfl, rfl, fun n bound column => ?_⟩
  replace bound : n < 4194304 := bound
  have rows := congrArg (·[column.val]) (SetupProofs.setupRow_eq n bound)
  simp only [setupRow, Vector.getElem_ofFn, Vector.getElem_map] at rows
  simp only [Fin.getElem_fin, Vector.getElem_map]
  exact rows

end Airbender.Keccak.Split.ColumnParity
