import Airbender.Review.Circuits.Blake2Worker.SecondAD

namespace Airbender.NativeWorkerSecondCB
open Airbender.NativeWorkerFirstG
abbrev F := ZMod mersenne31Modulus
def carry (w : Nat → F) (column : Fin 4) (limb : Fin 2) : F := w (306+46*column.val+limb.val)
def dByte (w : Nat → F) (column : Fin 4) (piece : Fin 4) : F := w (302+46*column.val+piece.val)
def dLimb (w : Nat → F) (column : Fin 4) (limb : Fin 2) : F :=
  if limb.val = 0 then dByte w column 1+256*dByte w column 2 else dByte w column 3+256*dByte w column 0
def bInput (w : Nat → F) (column : Fin 4) (limb : Fin 2) : F := Airbender.NativeWorkerSecondAD.bInput w column limb
def cInput (w : Nat → F) (column : Fin 4) (limb : Fin 2) : F := Airbender.NativeWorkerCB.cLimb w column limb
def cLimb (w : Nat → F) (column : Fin 4) (limb : Fin 2) : F :=
  cInput w column limb+dLimb w column limb+(if limb.val = 0 then 0 else carry w column 0)-65536*carry w column limb
def query (w : Nat → F) (column : Fin 4) (piece : Fin 4) : Vector F 4 :=
  Airbender.Blake2Worker.Native.fixedQuery w ⟨14+18*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩
def chunk7 (w : Nat → F) (column : Fin 4) (limb : Fin 2) : BitVec 7 := BitVec.ofNat 7 (w (310+46*column.val+2*limb.val)).val
def chunk9 (w : Nat → F) (column : Fin 4) (limb : Fin 2) : BitVec 9 := BitVec.ofNat 9 (w (311+46*column.val+2*limb.val)).val
/-- Actual native output chunks after rotate7. -/
def bAfter (w : Nat → F) (column : Fin 4) : BitVec 32 :=
  BitVec.append (BitVec.append (chunk7 w column 0) (chunk9 w column 1))
    (BitVec.append (chunk7 w column 1) (chunk9 w column 0))
structure LocalEffects (w : Nat → F) : Prop where
  carries : ∀ column : Fin 4, ∀ limb : Fin 2, (carry w column limb).val ≤ 1
  bounds : ∀ column : Fin 4, ∀ limb : Fin 2, (cLimb w column limb).val < 65536
  rotated : ∀ column : Fin 4, bAfter w column =
    (pack (bInput w column 0) (bInput w column 1) ^^^ pack (cLimb w column 0) (cLimb w column 1)).rotateRight 7
/-- Pure native G arithmetic reference; messages may be weighted multi-round words. -/
def g (a b c d x y : BitVec 32) : Vector (BitVec 32) 4 :=
  let a1 := a+b+x
  let d1 := (d ^^^ a1).rotateRight 16
  let c1 := c+d1
  let b1 := (b ^^^ c1).rotateRight 12
  let a2 := a1+b1+y
  let d2 := (d1 ^^^ a2).rotateRight 8
  let c2 := c1+d2
  let b2 := (b1 ^^^ c2).rotateRight 7
  #v[a2,b2,c2,d2]
/-- Actual four intermediate outputs, before diagonal calls/finalization. -/
def columnResult (w : Nat → F) (column : Fin 4) : Vector (BitVec 32) 4 :=
  #v[pack (Airbender.NativeWorkerSecondAD.sumLimb w column 0) (Airbender.NativeWorkerSecondAD.sumLimb w column 1),
    bAfter w column,pack (cLimb w column 0) (cLimb w column 1),Airbender.NativeWorkerSecondAD.dAfter w column]
structure RowEffects (w : Nat → F) : Prop where
  prior : Airbender.NativeWorkerSecondAD.RowEffects w
  mixing : LocalEffects w
  added : ∀ column : Fin 4, pack (cLimb w column 0) (cLimb w column 1) =
    pack (Airbender.NativeWorkerCB.cLimb w column 0) (Airbender.NativeWorkerCB.cLimb w column 1) + Airbender.NativeWorkerSecondAD.dAfter w column
  chained : ∀ column : Fin 4, bAfter w column =
    (Airbender.NativeWorkerCB.bAfter w column ^^^ pack (cLimb w column 0) (cLimb w column 1)).rotateRight 7
  complete : ∀ column : Fin 4, columnResult w column = g
    (Airbender.NativeWorkerAddition.preGWord w ⟨column.val,by have := column.isLt; omega⟩)
    (Airbender.NativeWorkerAddition.preGWord w ⟨4+column.val,by have := column.isLt; omega⟩)
    (Airbender.NativeWorkerAddition.preGWord w ⟨8+column.val,by have := column.isLt; omega⟩)
    (Airbender.NativeWorkerAddition.preGWord w ⟨12+column.val,by have := column.isLt; omega⟩)
    (Airbender.NativeWorkerAddition.messageWord w ⟨2*column.val,by have := column.isLt; omega⟩)
    (Airbender.NativeWorkerAddition.messageWord w ⟨2*column.val+1,by have := column.isLt; omega⟩)
end Airbender.NativeWorkerSecondCB
