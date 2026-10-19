import Airbender.Review.Helpers.Tables.WordROM

namespace Airbender.Verification

/-- Native 16-bit shift-amount input; its low five bits select the shift. -/
def truncateShiftRow (i : Fin 65536) : Vector Nat 3 := #v[i.val, i.val % 32, 0]

/-- Native width-three range query retains both zero padding columns. -/
def paddedRangeRow (i : Fin 65536) : Vector Nat 3 := #v[i.val, 0, 0]

/-- Lower and upper limbs of the RV32 sign-fill mask. Shift zero fills no bits.
    The key packs a high input limb below a five-bit shift amount. -/
def signFillLow (n : Nat) : Nat :=
  if n % 65536 < 32768 then 0 else 65536 - 2 ^ (32 - n / 65536)

def signFillHigh (n : Nat) : Nat :=
  if n % 65536 < 32768 then 0 else 65536 - 2 ^ (16 - min (n / 65536) 16)

def signFillRow (i : Fin 2097152) : Vector Nat 3 :=
  #v[i.val, signFillLow i.val, signFillHigh i.val]

/-- Original Clean static-table construction, shared by the three native helpers. -/
def shiftScalarTable {p : Nat} [Fact p.Prime] {length : Nat}
    (name : String) (rowNat : Fin length → Vector Nat 3) : Table (ZMod p) (fields 3) := .fromStatic {
  name := name
  length := length
  row i := (rowNat i).map Nat.cast
  index query := query[0].val
  Spec query := ∃ i, query = (rowNat i).map Nat.cast
  contains_iff _ := Iff.rfl
}

inductive ShiftScalarKind where
  | truncate | signFill | range
  deriving DecidableEq

def ShiftScalarKind.length : ShiftScalarKind → Nat
  | .truncate | .range => 65536 | .signFill => 2097152

def ShiftScalarKind.tag : ShiftScalarKind → Nat
  | .truncate => 47 | .signFill => 52 | .range => 53

def ShiftScalarKind.row (kind : ShiftScalarKind) : Fin kind.length → Vector Nat 3 :=
  match kind with
  | .truncate => truncateShiftRow | .signFill => signFillRow | .range => paddedRangeRow

def ShiftScalarKind.table {p : Nat} [Fact p.Prime] (kind : ShiftScalarKind) :
    Table (ZMod p) (fields 3) := shiftScalarTable "Airbender.V2ShiftScalar" kind.row

end Airbender.Verification
