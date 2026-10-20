import Airbender.Review.Helpers.Tables.WordROM

namespace Airbender.Verification.SubwordOffset
set_option autoImplicit false

/-- Native funct3 values that denote byte, halfword or word loads. -/
def validLoad (funct3 : Nat) : Bool :=
  funct3 == 0 || funct3 == 1 || funct3 == 2 || funct3 == 4 || funct3 == 5

/-- Native offset-table semantics, including the explicit misaligned-load-to-x0
    exception. Only the low address limb and decoder control bits form this key.
    This table alone does not establish accepted-row or architectural behavior. -/
def mask (key : Nat) : Nat :=
  let offset := key % 4
  let funct3 := key / 65536 % 8
  let less := funct3 == 0 || funct3 == 1 || funct3 == 4 || funct3 == 5
  let baseTrap := if funct3 == 2 then offset != 0
    else if funct3 == 1 || funct3 == 5 then offset % 2 != 0
    else if funct3 == 0 || funct3 == 4 then false else true
  let waived := validLoad funct3 && key / 524288 % 2 == 1 && key / 1048576 % 2 == 1
  (if less then 1 else 0) + (if 2 ≤ offset then 2 else 0) +
    (if baseTrap && !waived then 4 else 0)

def row (i : Fin 2097152) : Vector Nat 3 := #v[i.val, i.val % 4, mask i.val]

/-- All native offset/trap rows, without inserting a disabled query or removing
    misaligned/invalid keys. Literal native-data equality is proved under Proofs. -/
def table {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 3) := .fromStatic {
  name := "Airbender.V2SubwordOffsetMask"
  length := 2097152
  row i := (row i).map Nat.cast
  index query := query[0].val
  Spec query := ∃ i, query = (row i).map Nat.cast
  contains_iff _ := Iff.rfl
}

end Airbender.Verification.SubwordOffset
