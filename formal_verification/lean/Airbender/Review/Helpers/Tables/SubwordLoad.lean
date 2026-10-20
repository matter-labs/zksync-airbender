import Airbender.Review.Helpers.Tables.WordROM

namespace Airbender.Verification.SubwordLoad
set_option autoImplicit false

/-- Native load-table outputs for a preselected 16-bit limb, two-bit byte offset
    and raw funct3. Odd halfword and unused keys keep the native zero outputs;
    acceptance of those keys by the full decoder/circuit is a separate question. -/
def limbs (key : Nat) : Nat × Nat :=
  let limb := key % 65536
  let offset := key / 65536 % 4
  let funct3 := key / 262144 % 8
  let byte := if offset % 2 = 0 then limb % 256 else limb / 256
  if funct3 = 0 then
    (if byte < 128 then byte else byte + 65280, if byte < 128 then 0 else 65535)
  else if funct3 = 1 then
    if offset % 2 = 0 then (limb, if limb < 32768 then 0 else 65535) else (0, 0)
  else if funct3 = 4 then (byte, 0)
  else if funct3 = 5 then
    if offset % 2 = 0 then (limb, 0) else (0, 0)
  else (0, 0)

def row (i : Fin 2097152) : Vector Nat 3 := #v[i.val, (limbs i.val).1, (limbs i.val).2]

/-- The exact native load-data key space, retaining all unused/alignment keys.
    Complete equality to literal native rows is proved under Proofs. -/
def table {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 3) := .fromStatic {
  name := "Airbender.V2SubwordLoadData"
  length := 2097152
  row i := (row i).map Nat.cast
  index query := query[0].val
  Spec query := ∃ i, query = (row i).map Nat.cast
  contains_iff _ := Iff.rfl
}

end Airbender.Verification.SubwordLoad
