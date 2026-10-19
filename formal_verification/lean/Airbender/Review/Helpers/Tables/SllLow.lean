import Airbender.Review.Helpers.Tables.SllHigh

namespace Airbender.Verification

/-- High output limb of a logical shift of the low 16-bit input limb. -/
def sllLowHighOutput (key : Nat) : Nat :=
  (key % 65536 * 2 ^ (key / 65536) / 65536) % 65536

def sllLowRow (i : Fin 2097152) : Vector Nat 3 :=
  #v[i.val,sllHighOutput i.val,sllLowHighOutput i.val]

def sllLowTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 3) := .fromStatic {
  name := "Airbender.V2SllWith16BitInputLow"
  length := 2097152
  row i := (sllLowRow i).map Nat.cast
  index query := query[0].val
  Spec query := ∃ i, query = (sllLowRow i).map Nat.cast
  contains_iff _ := Iff.rfl
}

end Airbender.Verification
