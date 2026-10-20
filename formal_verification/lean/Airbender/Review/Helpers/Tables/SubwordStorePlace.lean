import Airbender.Review.Helpers.Tables.WordROM

namespace Airbender.Verification.SubwordStorePlace
set_option autoImplicit false

/-- Exact native contribution from the preselected value-to-write limb.
    SB places the low byte by offset parity; SH keeps the limb at every offset.
    SW and unused funct3 keys return zero. Full store acceptance is separate. -/
def placed (key : Nat) : Nat :=
  let limb := key % 65536
  let offset := key / 65536 % 4
  let funct3 := key / 262144 % 8
  if funct3 = 0 then
    if offset % 2 = 0 then limb % 256 else 256 * (limb % 256)
  else if funct3 = 1 then limb
  else 0

def row (i : Fin 2097152) : Vector Nat 3 := #v[i.val, placed i.val, 0]

def table {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 3) := .fromStatic {
  name := "Airbender.V2SubwordStorePlace"
  length := 2097152
  row i := (row i).map Nat.cast
  index query := query[0].val
  Spec query := ∃ i, query = (row i).map Nat.cast
  contains_iff _ := Iff.rfl
}

end Airbender.Verification.SubwordStorePlace
