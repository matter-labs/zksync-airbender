import Airbender.Review.Helpers.Tables.WordROM

namespace Airbender.Verification

/-- Native key: a 16-bit low input limb below a five-bit logical shift amount. -/
def srlLowOutput (key : Nat) : Nat := key % 65536 / 2 ^ (key / 65536)

def srlLowRow (i : Fin 2097152) : Vector Nat 3 := #v[i.val,srlLowOutput i.val,0]

def srlLowTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 3) := .fromStatic {
  name := "Airbender.V2SrlWith16BitInputLow"
  length := 2097152
  row i := (srlLowRow i).map Nat.cast
  index query := query[0].val
  Spec query := ∃ i, query = (srlLowRow i).map Nat.cast
  contains_iff _ := Iff.rfl
}

end Airbender.Verification
