import Airbender.Review.Circuits.Blake2Worker.DiagonalFirst

namespace Airbender.NativeWorkerDiagonalCB
abbrev F := ZMod mersenne31Modulus
def carry (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : F := w (462+44*diagonal.val+limb.val)
def dByte (w : Nat → F) (diagonal piece : Fin 4) : F := w (458+44*diagonal.val+piece.val)
def dLimb (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : F :=
  if limb.val = 0 then dByte w diagonal 2+256*dByte w diagonal 3 else dByte w diagonal 0+256*dByte w diagonal 1
def bInput (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : F := Airbender.NativeWorkerDiagonalFirst.inputLimb w diagonal 1 limb
def cInput (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : F := Airbender.NativeWorkerDiagonalFirst.inputLimb w diagonal 2 limb
def cLimb (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : F :=
  cInput w diagonal limb+dLimb w diagonal limb+(if limb.val=0 then 0 else carry w diagonal 0)-65536*carry w diagonal limb
def query (w : Nat → F) (diagonal : Fin 4) (piece : Fin 6) : Vector F 4 :=
  Airbender.Blake2Worker.Native.fixedQuery w ⟨76+18*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩
def chunk3 (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : BitVec 3 := BitVec.ofNat 3 (w (470+44*diagonal.val+5*limb.val)).val
def chunk9 (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : BitVec 9 := BitVec.ofNat 9 (w (471+44*diagonal.val+5*limb.val)).val
def chunk4 (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : BitVec 4 := BitVec.ofNat 4 (w (472+44*diagonal.val+5*limb.val)).val
def bAfter (w : Nat → F) (diagonal : Fin 4) : BitVec 32 :=
  BitVec.append (BitVec.append (BitVec.append (chunk9 w diagonal 0) (chunk3 w diagonal 0)) (chunk4 w diagonal 1))
    (BitVec.append (BitVec.append (chunk9 w diagonal 1) (chunk3 w diagonal 1)) (chunk4 w diagonal 0))
structure LocalEffects (w : Nat → F) : Prop where
  carries : ∀ diagonal : Fin 4, ∀ limb : Fin 2, (carry w diagonal limb).val ≤ 1
  bounds : ∀ diagonal : Fin 4, ∀ limb : Fin 2, (cLimb w diagonal limb).val < 65536 ∧ (bInput w diagonal limb).val < 65536
  rotated : ∀ diagonal : Fin 4, bAfter w diagonal =
    (Airbender.NativeWorkerFirstG.pack (bInput w diagonal 0) (bInput w diagonal 1) ^^^
      Airbender.NativeWorkerFirstG.pack (cLimb w diagonal 0) (cLimb w diagonal 1)).rotateRight 12
/-- Pure first half of G, with a possibly weighted message word. -/
def firstHalf (a b c d x : BitVec 32) : Vector (BitVec 32) 4 :=
  let a1 := a+b+x
  let d1 := (d ^^^ a1).rotateRight 16
  let c1 := c+d1
  let b1 := (b ^^^ c1).rotateRight 12
  #v[a1,b1,c1,d1]
def halfResult (w : Nat → F) (diagonal : Fin 4) : Vector (BitVec 32) 4 :=
  #v[Airbender.NativeWorkerDiagonalFirst.aAfter w diagonal,bAfter w diagonal,
    Airbender.NativeWorkerFirstG.pack (cLimb w diagonal 0) (cLimb w diagonal 1),Airbender.NativeWorkerDiagonalFirst.dAfter w diagonal]
structure RowEffects (w : Nat → F) : Prop where
  prior : Airbender.NativeWorkerDiagonalFirst.RowEffects w
  mixing : LocalEffects w
  added : ∀ diagonal : Fin 4, Airbender.NativeWorkerFirstG.pack (cLimb w diagonal 0) (cLimb w diagonal 1) =
    Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 2+Airbender.NativeWorkerDiagonalFirst.dAfter w diagonal
  complete : ∀ diagonal : Fin 4, halfResult w diagonal = firstHalf
    (Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 0)
    (Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 1)
    (Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 2)
    (Airbender.NativeWorkerDiagonalFirst.inputWord w diagonal 3)
    (Airbender.NativeWorkerAddition.messageWord w ⟨8+2*diagonal.val,by have := diagonal.isLt; omega⟩)
end Airbender.NativeWorkerDiagonalCB
