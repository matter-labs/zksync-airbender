import Airbender.Import.Setup

namespace Airbender.Setup

def packedByte (payload index : Nat) : Nat := (payload >>> (8 * index)) % 256

def packedArray (length payload : Nat) : Array Nat :=
  Array.ofFn fun index : Fin length => packedByte payload index.val

/-- Lossless payload data for the three existing source block constructors. -/
inductive PackedBlock where
  | affine (length first : Nat) (stride : Int)
  | dense (length payload : Nat)
  | periodic (count : Nat) (stride : Int) (period payload : Nat)
  deriving Repr

def PackedBlock.decode : PackedBlock → Block
  | .affine length first stride => .affine length first stride
  | .dense length payload => .dense (packedArray length payload)
  | .periodic count stride period payload => .periodic count stride (packedArray period payload)

def PackedBlock.length : PackedBlock → Nat
  | .affine length _ _ => length
  | .dense length _ => length
  | .periodic count _ period _ => count * period

structure PackedRunInput where
  count : Nat
  stride : Nat
  period : Nat
  payload : Nat

def PackedBlock.input : PackedBlock → Option PackedRunInput
  | .affine length first (.ofNat stride) => some ⟨length, stride, 1, first⟩
  | .dense length payload => some ⟨1, 0, length, payload⟩
  | .periodic count (.ofNat stride) period payload => some ⟨count, stride, period, payload⟩
  | _ => none

end Airbender.Setup
