import Airbender.Review.Helpers.Tables.WordROM

namespace Airbender.Verification

/-- Native RangeCheckSmall ID 8 enumerates first then second byte, with a
    retained third zero column. Exported data fidelity is checked separately. -/
def smallRangeRow (i : Fin 65536) : Vector Nat 3 :=
  #v[i.val / 256, i.val % 256, 0]

def smallRangeTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 3) := .fromStatic {
  name := "Airbender.V2RangeCheckSmall"
  length := 65536
  row i := (smallRangeRow i).map Nat.cast
  index query := query[0].val * 256 + query[1].val
  Spec query := ∃ i, query = (smallRangeRow i).map Nat.cast
  contains_iff _ := Iff.rfl
}

end Airbender.Verification
