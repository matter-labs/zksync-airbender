import Sail.BitVec

namespace Airbender.Arithmetic

def limbBase : Nat := 65536
def wordModulus : Nat := 4294967296

/-- Airbender's two-limb representation, shared across circuit families. -/
structure Word where
  lo : Nat
  hi : Nat
  deriving Repr, DecidableEq

def Word.value (word : Word) : Nat := word.lo + limbBase * word.hi
def Word.Bounded (word : Word) : Prop := word.lo < limbBase ∧ word.hi < limbBase
def Word.toBitVec (word : Word) : BitVec 32 := BitVec.ofNat 32 word.value

/-- Canonical two-limb encoding of an architectural word. -/
def Word.ofBitVec (bits : BitVec 32) : Word :=
  ⟨bits.toNat % limbBase, bits.toNat / limbBase⟩

end Airbender.Arithmetic
