import Airbender.Review.Circuits.Blake2Worker.ColumnCB

namespace Airbender.NativeWorkerSecondAD
open Airbender.NativeWorkerFirstG
abbrev F := ZMod mersenne31Modulus
def carryBit (w : Nat → F) (column : Fin 4) (slot : Fin 4) : F := w (296+46*column.val+slot.val)
def carry (w : Nat → F) (column : Fin 4) (limb : Fin 2) : F :=
  w (296+46*column.val+2*limb.val)+2*w (297+46*column.val+2*limb.val)
def bInput (w : Nat → F) (column : Fin 4) (limb : Fin 2) : F :=
  if limb.val = 0 then w (290+46*column.val)+16*w (293+46*column.val)+128*w (294+46*column.val)
  else w (295+46*column.val)+16*w (288+46*column.val)+128*w (289+46*column.val)
def sumLimb (w : Nat → F) (column : Fin 4) (limb : Fin 2) : F :=
  Airbender.NativeWorkerFirstG.sumLimb w column limb + bInput w column limb +
  Airbender.NativeWorkerSchedule.selected w ⟨2*column.val+1,by have := column.isLt; omega⟩ limb +
  (if limb.val = 0 then 0 else carry w column 0)-65536*carry w column limb
def dInput (w : Nat → F) (column : Fin 4) (limb : Fin 2) : F := Airbender.NativeWorkerCB.dLimb w column limb
def query (w : Nat → F) (column : Fin 4) (piece : Fin 4) : Vector F 4 :=
  Airbender.Blake2Worker.Native.fixedQuery w ⟨10+18*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩
def byte (w : Nat → F) (column : Fin 4) (piece : Fin 4) : BitVec 8 := BitVec.ofNat 8 (w (302+46*column.val+piece.val)).val
/-- Actual four output bytes after native rotateRight8. -/
def dAfter (w : Nat → F) (column : Fin 4) : BitVec 32 :=
  BitVec.append (BitVec.append (byte w column 0) (byte w column 3))
    (BitVec.append (byte w column 2) (byte w column 1))
structure LocalEffects (w : Nat → F) : Prop where
  carries : ∀ column : Fin 4, ∀ slot : Fin 4, (carryBit w column slot).val ≤ 1
  bounds : ∀ column : Fin 4, ∀ limb : Fin 2, (sumLimb w column limb).val < 65536 ∧ (dInput w column limb).val < 65536
  rotated : ∀ column : Fin 4, dAfter w column =
    (pack (dInput w column 0) (dInput w column 1) ^^^ pack (sumLimb w column 0) (sumLimb w column 1)).rotateRight 8
structure RowEffects (w : Nat → F) : Prop where
  prior : Airbender.NativeWorkerCB.RowEffects w
  mixing : LocalEffects w
  bBounds : ∀ column : Fin 4, ∀ limb : Fin 2, (bInput w column limb).val < 65536
  carries : ∀ column : Fin 4, ∀ limb : Fin 2, (carry w column limb).val ≤ 3
  chained : ∀ column : Fin 4, dAfter w column =
    (Airbender.NativeWorkerFirstG.dAfter w column ^^^ pack (sumLimb w column 0) (sumLimb w column 1)).rotateRight 8
  added : ∀ column : Fin 4, pack (sumLimb w column 0) (sumLimb w column 1) =
    Airbender.NativeWorkerAddition.aAfter w column + Airbender.NativeWorkerCB.bAfter w column +
      Airbender.NativeWorkerAddition.messageWord w ⟨2*column.val+1,by have := column.isLt; omega⟩
end Airbender.NativeWorkerSecondAD
