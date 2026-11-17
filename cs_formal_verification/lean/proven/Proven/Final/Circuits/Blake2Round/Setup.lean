module
public import Human.Circuits.Blake2Round.Tables.SetupImport
public import Proven.Blake2Round.Setup.Rows

@[expose] public section

namespace Airbender.Blake2Round

/-- The claimed formula rows are the row formulas that the kernel scans check. -/
theorem formulaRow_eq (n : Nat) : formulaRow n = SetupProofs.formulaRow n := rfl

/-- Each column of the imported round setup is its row formula (kernel scans), on all 2^20 rows. -/
theorem setup_import : SetupImportClaim := by
  refine ⟨rfl, rfl, fun n bound column => ?_⟩
  replace bound : n < 1048576 := bound
  have rows := congrArg (·[column.val]) (SetupProofs.setupRow_eq n bound)
  simp only [setupRow, Vector.getElem_ofFn, Vector.getElem_map, ← formulaRow_eq] at rows
  simp only [Fin.getElem_fin, Vector.getElem_map]
  exact rows

end Airbender.Blake2Round
