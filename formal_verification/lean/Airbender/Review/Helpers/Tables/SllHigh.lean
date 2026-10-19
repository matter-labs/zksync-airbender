import Airbender.Review.Helpers.Tables.WordROM

namespace Airbender.Verification

/-- High output limb of a logical shift of the high 16-bit input limb. -/
def sllHighOutput (key : Nat) : Nat := (key % 65536 * 2 ^ (key / 65536)) % 65536

def sllHighRow (i : Fin 2097152) : Vector Nat 3 := #v[i.val,0,sllHighOutput i.val]

def sllHighTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 3) := .fromStatic {
  name := "Airbender.V2SllWith16BitInputHigh"
  length := 2097152
  row i := (sllHighRow i).map Nat.cast
  index query := query[0].val
  Spec query := ∃ i, query = (sllHighRow i).map Nat.cast
  contains_iff _ := Iff.rfl
}

end Airbender.Verification
