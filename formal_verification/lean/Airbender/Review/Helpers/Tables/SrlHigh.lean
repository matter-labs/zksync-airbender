import Airbender.Review.Helpers.Tables.SrlLow

namespace Airbender.Verification

/-- Low output limb of a logical shift of the high 16-bit input limb. -/
def srlHighLowOutput (key : Nat) : Nat :=
  (key % 65536 * 65536 / 2 ^ (key / 65536)) % 65536

def srlHighRow (i : Fin 2097152) : Vector Nat 3 :=
  #v[i.val,srlHighLowOutput i.val,srlLowOutput i.val]

def srlHighTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 3) := .fromStatic {
  name := "Airbender.V2SrlWith16BitInputHigh"
  length := 2097152
  row i := (srlHighRow i).map Nat.cast
  index query := query[0].val
  Spec query := ∃ i, query = (srlHighRow i).map Nat.cast
  contains_iff _ := Iff.rfl
}

end Airbender.Verification
