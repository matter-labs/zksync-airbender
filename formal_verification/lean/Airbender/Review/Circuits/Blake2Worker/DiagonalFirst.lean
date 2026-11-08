import Airbender.Review.Circuits.Blake2Worker.SecondCB

namespace Airbender.NativeWorkerDiagonalFirst
open Airbender.NativeWorkerFirstG
abbrev F := ZMod mersenne31Modulus
/-- Actual post-column B limbs, with native 9/7-bit rotated chunk order. -/
def bLimb (w : Nat → F) (column : Fin 4) (limb : Fin 2) : F :=
  if limb.val = 0 then w (311+46*column.val)+512*w (312+46*column.val)
  else w (313+46*column.val)+512*w (310+46*column.val)
def columnLimb (w : Nat → F) (column component : Fin 4) (limb : Fin 2) : F :=
  match component.val with
  | 0 => Airbender.NativeWorkerSecondAD.sumLimb w column limb
  | 1 => bLimb w column limb
  | 2 => Airbender.NativeWorkerSecondCB.cLimb w column limb
  | _ => Airbender.NativeWorkerSecondCB.dLimb w column limb
/-- Native diagonal permutation A[i], B[i+1], C[i+2], D[i+3]. -/
def sourceColumn (diagonal component : Fin 4) : Fin 4 := ⟨(diagonal.val+component.val)%4,Nat.mod_lt _ (by decide)⟩
def inputLimb (w : Nat → F) (diagonal component : Fin 4) (limb : Fin 2) : F :=
  columnLimb w (sourceColumn diagonal component) component limb
def inputWord (w : Nat → F) (diagonal component : Fin 4) : BitVec 32 :=
  pack (inputLimb w diagonal component 0) (inputLimb w diagonal component 1)
def carryBit (w : Nat → F) (diagonal slot : Fin 4) : F := w (452+44*diagonal.val+slot.val)
def carry (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : F :=
  w (452+44*diagonal.val+2*limb.val)+2*w (453+44*diagonal.val+2*limb.val)
def sumLimb (w : Nat → F) (diagonal : Fin 4) (limb : Fin 2) : F :=
  inputLimb w diagonal 0 limb+ inputLimb w diagonal 1 limb+
    Airbender.NativeWorkerSchedule.selected w ⟨8+2*diagonal.val,by have := diagonal.isLt; omega⟩ limb+
    (if limb.val = 0 then 0 else carry w diagonal 0)-65536*carry w diagonal limb
def query (w : Nat → F) (diagonal piece : Fin 4) : Vector F 4 :=
  Airbender.Blake2Worker.Native.fixedQuery w ⟨72+18*diagonal.val+piece.val,by have := diagonal.isLt; have := piece.isLt; omega⟩
def byte (w : Nat → F) (diagonal piece : Fin 4) : BitVec 8 := BitVec.ofNat 8 (w (458+44*diagonal.val+piece.val)).val
def dAfter (w : Nat → F) (diagonal : Fin 4) : BitVec 32 :=
  BitVec.append (BitVec.append (byte w diagonal 1) (byte w diagonal 0))
    (BitVec.append (byte w diagonal 3) (byte w diagonal 2))
def aAfter (w : Nat → F) (diagonal : Fin 4) : BitVec 32 := pack (sumLimb w diagonal 0) (sumLimb w diagonal 1)
structure LocalEffects (w : Nat → F) : Prop where
  carries : ∀ diagonal slot : Fin 4, (carryBit w diagonal slot).val ≤ 1
  bounds : ∀ diagonal : Fin 4, ∀ limb : Fin 2, (sumLimb w diagonal limb).val < 65536
  rotated : ∀ diagonal : Fin 4, dAfter w diagonal = (inputWord w diagonal 3 ^^^ aAfter w diagonal).rotateRight 16
structure RowEffects (w : Nat → F) : Prop where
  prior : Airbender.NativeWorkerSecondCB.RowEffects w
  inputs : ∀ diagonal component : Fin 4, ∀ limb : Fin 2, (inputLimb w diagonal component limb).val < 65536
  routed : ∀ diagonal component : Fin 4, inputWord w diagonal component =
    (Airbender.NativeWorkerSecondCB.columnResult w (sourceColumn diagonal component))[component]
  mixing : LocalEffects w
  carryBounds : ∀ diagonal : Fin 4, ∀ limb : Fin 2, (carry w diagonal limb).val ≤ 3
  added : ∀ diagonal : Fin 4, aAfter w diagonal = inputWord w diagonal 0+ inputWord w diagonal 1+
    Airbender.NativeWorkerAddition.messageWord w ⟨8+2*diagonal.val,by have := diagonal.isLt; omega⟩
end Airbender.NativeWorkerDiagonalFirst
