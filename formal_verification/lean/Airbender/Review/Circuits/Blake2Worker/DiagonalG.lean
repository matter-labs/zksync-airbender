import Airbender.Review.Circuits.Blake2Worker.DiagonalAD

namespace Airbender.NativeWorkerDiagonalG
open Airbender.NativeWorkerFirstG
abbrev F := ZMod mersenne31Modulus
def carry (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : F := w (488+44*diagonal.val+limb.val)
def dByte (w : Nat → F) (diagonal : Fin 4) (piece : Fin 4) : F := w (484+44*diagonal.val+piece.val)
def dLimb (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : F :=
  if limb.val = 0 then dByte w diagonal 1+256*dByte w diagonal 2 else dByte w diagonal 3+256*dByte w diagonal 0
def bInput (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : F := Airbender.NativeWorkerDiagonalAD.bInput w diagonal limb
def cInput (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : F := Airbender.NativeWorkerDiagonalCB.cLimb w diagonal limb
def cLimb (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : F :=
  cInput w diagonal limb+dLimb w diagonal limb+(if limb.val = 0 then 0 else carry w diagonal 0)-65536*carry w diagonal limb
def query (w : Nat → F) (diagonal : Fin 4) (piece : Fin 4) : Vector F 4 :=
  Airbender.Blake2Worker.Native.fixedQuery w ⟨86+18*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩
def chunk7 (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : BitVec 7 := BitVec.ofNat 7 (w (492+44*diagonal.val+2*limb.val)).val
def chunk9 (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : BitVec 9 := BitVec.ofNat 9 (w (493+44*diagonal.val+2*limb.val)).val
/-- Actual native output chunks after rotate7. -/
def bAfter (w : Nat → F) (diagonal : Fin 4) : BitVec 32 :=
  BitVec.append (BitVec.append (chunk7 w diagonal 0) (chunk9 w diagonal 1))
    (BitVec.append (chunk7 w diagonal 1) (chunk9 w diagonal 0))
structure LocalEffects (w : Nat → F) : Prop where
  carries : ∀ diagonal : Fin 4, ∀ limb : Fin 2, (carry w diagonal limb).val ≤ 1
  bounds : ∀ diagonal : Fin 4, ∀ limb : Fin 2, (cLimb w diagonal limb).val < 65536
  rotated : ∀ diagonal : Fin 4, bAfter w diagonal =
    (pack (bInput w diagonal 0) (bInput w diagonal 1) ^^^ pack (cLimb w diagonal 0) (cLimb w diagonal 1)).rotateRight 7
/-- Actual four intermediate outputs, before diagonal calls/finalization. -/
def diagonalResult (w : Nat → F) (diagonal : Fin 4) : Vector (BitVec 32) 4 :=
  #v[pack (Airbender.NativeWorkerDiagonalAD.sumLimb w diagonal 0) (Airbender.NativeWorkerDiagonalAD.sumLimb w diagonal 1),
    bAfter w diagonal,pack (cLimb w diagonal 0) (cLimb w diagonal 1),Airbender.NativeWorkerDiagonalAD.dAfter w diagonal]
structure RowEffects (w : Nat → F) : Prop where
  prior : Airbender.NativeWorkerDiagonalAD.RowEffects w
  mixing : LocalEffects w
  added : ∀ diagonal : Fin 4, pack (cLimb w diagonal 0) (cLimb w diagonal 1) =
    pack (Airbender.NativeWorkerDiagonalCB.cLimb w diagonal 0) (Airbender.NativeWorkerDiagonalCB.cLimb w diagonal 1) + Airbender.NativeWorkerDiagonalAD.dAfter w diagonal
  chained : ∀ diagonal : Fin 4, bAfter w diagonal =
    (Airbender.NativeWorkerDiagonalCB.bAfter w diagonal ^^^ pack (cLimb w diagonal 0) (cLimb w diagonal 1)).rotateRight 7
  complete : ∀ diagonal : Fin 4, diagonalResult w diagonal = Airbender.NativeWorkerSecondCB.g
    (Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 0)
    (Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 1)
    (Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 2)
    (Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 3)
    (Airbender.NativeWorkerAddition.messageWord w ⟨8+2*diagonal.val,by have := diagonal.isLt; omega⟩)
    (Airbender.NativeWorkerAddition.messageWord w ⟨9+2*diagonal.val,by have := diagonal.isLt; omega⟩)
end Airbender.NativeWorkerDiagonalG
