import Airbender.Review.Circuits.Blake2Worker.Addition

namespace Airbender.NativeWorkerCB
open Airbender.NativeWorkerInitial Airbender.NativeWorkerFirstG
abbrev F := ZMod mersenne31Modulus
def carry (w : Nat → F) (column : Fin 4) (limb : Fin 2) : F := w (280+46*column.val+limb.val)
def dByte (w : Nat → F) (column : Fin 4) (piece : Fin 4) : F := w (275+46*column.val+piece.val+piece.val/2)
def dLimb (w : Nat → F) (column : Fin 4) (limb : Fin 2) : F :=
  if limb.val = 0 then dByte w column 2+256*dByte w column 3 else dByte w column 0+256*dByte w column 1
def bInput (w : Nat → F) (column : Fin 4) (limb : Fin 2) : F :=
  observed w ⟨4+column.val,by have := column.isLt; omega⟩ limb
def cInput (w : Nat → F) (column : Fin 4) (limb : Fin 2) : F :=
  observed w ⟨8+column.val,by have := column.isLt; omega⟩ limb
def cLimb (w : Nat → F) (column : Fin 4) (limb : Fin 2) : F :=
  cInput w column limb+dLimb w column limb+(if limb.val = 0 then 0 else carry w column 0)-65536*carry w column limb
def query (w : Nat → F) (column : Fin 4) (piece : Fin 6) : Vector F 4 :=
  Airbender.Blake2Worker.Native.fixedQuery w ⟨4+18*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩
def chunk3 (w : Nat → F) (column : Fin 4) (limb : Fin 2) : BitVec 3 := BitVec.ofNat 3 (w (288+46*column.val+5*limb.val)).val
def chunk9 (w : Nat → F) (column : Fin 4) (limb : Fin 2) : BitVec 9 := BitVec.ofNat 9 (w (289+46*column.val+5*limb.val)).val
def chunk4 (w : Nat → F) (column : Fin 4) (limb : Fin 2) : BitVec 4 := BitVec.ofNat 4 (w (290+46*column.val+5*limb.val)).val
/-- Actual native chunk order after rotate12; no expected result premise. -/
def bAfter (w : Nat → F) (column : Fin 4) : BitVec 32 :=
  BitVec.append (BitVec.append (BitVec.append (chunk9 w column 0) (chunk3 w column 0)) (chunk4 w column 1))
    (BitVec.append (BitVec.append (chunk9 w column 1) (chunk3 w column 1)) (chunk4 w column 0))
structure LocalEffects (w : Nat → F) : Prop where
  carries : ∀ column : Fin 4, ∀ limb : Fin 2, (carry w column limb).val ≤ 1
  bounds : ∀ column : Fin 4, ∀ limb : Fin 2, (cLimb w column limb).val < 65536 ∧ (bInput w column limb).val < 65536
  rotated : ∀ column : Fin 4, bAfter w column =
    (pack (bInput w column 0) (bInput w column 1) ^^^ pack (cLimb w column 0) (cLimb w column 1)).rotateRight 12
structure RowEffects (w : Nat → F) : Prop where
  prior : Airbender.NativeWorkerAddition.RowEffects w
  mixing : LocalEffects w
  added : ∀ column : Fin 4, pack (cLimb w column 0) (cLimb w column 1) =
    Airbender.NativeWorkerAddition.preGWord w ⟨8+column.val,by have := column.isLt; omega⟩ + dAfter w column
end Airbender.NativeWorkerCB
