import Airbender.Review.Helpers.Tables.WordROM
import Mathlib.Data.Nat.Bitwise

namespace Airbender.Verification

inductive BinaryKind where
  | xor | or | and
  deriving DecidableEq

def BinaryKind.tag : BinaryKind → Nat
  | .xor => 4 | .or => 6 | .and => 7

def BinaryKind.apply (kind : BinaryKind) (a b : Nat) : Nat :=
  match kind with
  | .xor => a ^^^ b | .or => a ||| b | .and => a &&& b

-- Unchanged mathematical byte-operation definition from the pinned source.
def byteOperation {n : Nat} (tag : Nat) (a b : BitVec n) : BitVec n :=
  if tag = 4 then a ^^^ b else if tag = 6 then a ||| b else a &&& b

def binaryRow (kind : BinaryKind) (i : Fin 65536) : Vector Nat 3 :=
  #v[i.val / 256,i.val % 256,kind.apply (i.val / 256) (i.val % 256)]

/-- Exact three-column membership, connected to actual exported rows separately. -/
def binaryTable {p : Nat} [Fact p.Prime] (kind : BinaryKind) : Table (ZMod p) (fields 3) := .fromStatic {
  name := "Airbender.V2Binary"
  length := 65536
  row i := (binaryRow kind i).map Nat.cast
  index query := query[0].val * 256 + query[1].val
  Spec query := ∃ i, query = (binaryRow kind i).map Nat.cast
  contains_iff _ := Iff.rfl
}

end Airbender.Verification
