import Airbender.Review.Circuits.Blake2Worker.DiagonalCB

namespace Airbender.NativeWorkerDiagonalAD
open Airbender.NativeWorkerFirstG
abbrev F := ZMod mersenne31Modulus
def carryBit (w : Nat → F) (diagonal : Fin 4) (slot : Fin 4) : F := w (478+44*diagonal.val+slot.val)
def carry (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : F :=
  w (478+44*diagonal.val+2*limb.val)+2*w (479+44*diagonal.val+2*limb.val)
def bInput (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : F :=
  if limb.val = 0 then w (472+44*diagonal.val)+16*w (475+44*diagonal.val)+128*w (476+44*diagonal.val)
  else w (477+44*diagonal.val)+16*w (470+44*diagonal.val)+128*w (471+44*diagonal.val)
def sumLimb (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : F :=
  Airbender.NativeWorkerDiagonalFirst.sumLimb w diagonal limb + bInput w diagonal limb +
  Airbender.NativeWorkerSchedule.selected w ⟨9+2*diagonal.val,by have := diagonal.isLt; omega⟩ limb +
  (if limb.val = 0 then 0 else carry w diagonal 0)-65536*carry w diagonal limb
def dInput (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : F := Airbender.NativeWorkerDiagonalCB.dLimb w diagonal limb
def query (w : Nat → F) (diagonal : Fin 4) (piece : Fin 4) : Vector F 4 :=
  Airbender.Blake2Worker.Native.fixedQuery w ⟨82+18*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩
def byte (w : Nat → F) (diagonal : Fin 4) (piece : Fin 4) : BitVec 8 := BitVec.ofNat 8 (w (484+44*diagonal.val+piece.val)).val
/-- Actual four output bytes after native rotateRight8. -/
def dAfter (w : Nat → F) (diagonal : Fin 4) : BitVec 32 :=
  BitVec.append (BitVec.append (byte w diagonal 0) (byte w diagonal 3))
    (BitVec.append (byte w diagonal 2) (byte w diagonal 1))
structure LocalEffects (w : Nat → F) : Prop where
  carries : ∀ diagonal : Fin 4, ∀ slot : Fin 4, (carryBit w diagonal slot).val ≤ 1
  bounds : ∀ diagonal : Fin 4, ∀ limb : Fin 2, (sumLimb w diagonal limb).val < 65536 ∧ (dInput w diagonal limb).val < 65536
  rotated : ∀ diagonal : Fin 4, dAfter w diagonal =
    (pack (dInput w diagonal 0) (dInput w diagonal 1) ^^^ pack (sumLimb w diagonal 0) (sumLimb w diagonal 1)).rotateRight 8
structure RowEffects (w : Nat → F) : Prop where
  prior : Airbender.NativeWorkerDiagonalCB.RowEffects w
  mixing : LocalEffects w
  bBounds : ∀ diagonal : Fin 4, ∀ limb : Fin 2, (bInput w diagonal limb).val < 65536
  carries : ∀ diagonal : Fin 4, ∀ limb : Fin 2, (carry w diagonal limb).val ≤ 3
  chained : ∀ diagonal : Fin 4, dAfter w diagonal =
    (Airbender.NativeWorkerDiagonalFirst.dAfter w diagonal ^^^ pack (sumLimb w diagonal 0) (sumLimb w diagonal 1)).rotateRight 8
  added : ∀ diagonal : Fin 4, pack (sumLimb w diagonal 0) (sumLimb w diagonal 1) =
    Airbender.NativeWorkerDiagonalFirst.aAfter w diagonal + Airbender.NativeWorkerDiagonalCB.bAfter w diagonal +
      Airbender.NativeWorkerAddition.messageWord w ⟨9+2*diagonal.val,by have := diagonal.isLt; omega⟩
end Airbender.NativeWorkerDiagonalAD
