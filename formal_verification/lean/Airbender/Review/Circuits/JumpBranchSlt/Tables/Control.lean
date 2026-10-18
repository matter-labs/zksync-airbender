import Airbender.Review.Helpers.Tables.WordROM

namespace Airbender.Verification

/-- Native four input flags: unsigned borrow, equality and both operand signs. -/
def controlFlag (bits funct3 : Nat) : Bool :=
  let unsigned := bits % 2 == 1
  let equal := bits / 2 % 2 == 1
  let sign1 := bits / 4 % 2 == 1
  let sign2 := bits / 8 % 2 == 1
  let signed := if sign1 != sign2 then sign1 else unsigned
  match funct3 with
  | 0 => equal | 1 => !equal | 2 => signed | 3 => unsigned
  | 4 => signed | 5 => !signed | 6 => unsigned | _ => !unsigned

/-- Actual v2 triple: separate four-bit flags, raw funct3 and one result bit. -/
def conditionalControlRow (i : Fin 128) : Vector Nat 3 :=
  #v[i.val / 8, i.val % 8, if controlFlag (i.val / 8) (i.val % 8) then 1 else 0]

/-- Native low-PC cleanup: keep bit one and clear both low bits of the result. -/
def jumpCleanupRow (i : Fin 65536) : Vector Nat 3 :=
  #v[i.val, i.val / 2 % 2, 4 * (i.val / 4)]

def conditionalControlTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 3) := .fromStatic {
  name := "Airbender.V2ConditionalJmpBranchSlt"
  length := 128
  row i := (conditionalControlRow i).map Nat.cast
  index query := query[0].val * 8 + query[1].val
  Spec query := ∃ i, query = (conditionalControlRow i).map Nat.cast
  contains_iff _ := Iff.rfl
}

def jumpCleanupTable {p : Nat} [Fact p.Prime] : Table (ZMod p) (fields 3) := .fromStatic {
  name := "Airbender.V2JumpCleanupOffset"
  length := 65536
  row i := (jumpCleanupRow i).map Nat.cast
  index query := query[0].val
  Spec query := ∃ i, query = (jumpCleanupRow i).map Nat.cast
  contains_iff _ := Iff.rfl
}

end Airbender.Verification
