import Airbender.Data.Setup.Blake2Round.XorData

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true

theorem xorRegionRow_read (kind : Fin 6) (n j : Nat) (hj : j < 6) :
    (xorRegionRow kind n)[j] = ((xorData kind).columns[j].get? n).getD 0 := by
  simp only [xorRegionRow, Vector.getElem_map]

theorem row_from_entries (kind : Fin 6) (n : Nat) (expected : Vector Nat 6)
    (columns : ∀ (j : Nat) (_hj : j < 6), (xorData kind).columns[j].get? n = some expected[j]) :
    xorRegionRow kind n = expected := by
  apply Vector.ext
  intro j hj
  rw [xorRegionRow_read kind n j hj, columns j hj, Option.getD_some]

end Airbender.Blake2Round.Proofs
