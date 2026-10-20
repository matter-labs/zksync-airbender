import Airbender.Review.Helpers.Tables.WordROM

namespace Airbender.Verification.SubwordStoreClear
set_option autoImplicit false

/-- Exact native clearing of a preselected original RAM limb. SB retains the
    byte not overwritten at the chosen offset; all other funct3 keys return zero.
    Full native limb selection and instruction acceptance remain separate. -/
def cleared (key : Nat) : Nat :=
  let limb := key % 65536
  let offset := key / 65536 % 4
  let funct3 := key / 262144 % 8
  if funct3 = 0 then
    if offset % 2 = 0 then 256 * (limb / 256) else limb % 256
  else 0

def row (i : Fin 2097152) : Vector Nat 3 := #v[i.val, cleared i.val, 0]

/-- Original Clean static relation over the complete native 21-bit key domain. -/
def table {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 3) := .fromStatic {
  name := "Airbender.V2SubwordStoreClear"
  length := 2097152
  row i := (row i).map Nat.cast
  index query := query[0].val
  Spec query := ∃ i, query = (row i).map Nat.cast
  contains_iff _ := Iff.rfl
}

end Airbender.Verification.SubwordStoreClear
