import Airbender.Review.Circuits.Blake2Worker.Queries
import Airbender.Review.Circuits.Blake2Worker.StateInitialization

namespace Airbender.NativeWorkerFirstG
open Airbender.Blake2Worker.Native Airbender.NativeWorkerInitial Airbender.NativeWorkerSchedule
abbrev F := ZMod mersenne31Modulus
def carryBit (w : Nat → F) (column : Fin 4) (slot : Fin 4) : F := w (268+46*column.val+slot.val)
/-- Both actual carry bits, with native weights1 and2; no one-hot claim. -/
def carry (w : Nat → F) (column : Fin 4) (limb : Fin 2) : F :=
  w (268+46*column.val+2*limb.val)+2*w (269+46*column.val+2*limb.val)
/-- Actual first tri-addition, as field limbs with its original carry variables. -/
def sumLimb (w : Nat → F) (column : Fin 4) (limb : Fin 2) : F :=
  observed w ⟨column.val,by have := column.isLt; omega⟩ limb +
  observed w ⟨4+column.val,by have := column.isLt; omega⟩ limb +
  selected w ⟨2*column.val,by have := column.isLt; omega⟩ limb +
  (if limb.val = 0 then 0 else carry w column 0) - 65536*carry w column limb
def dInput (w : Nat → F) (column : Fin 4) (limb : Fin 2) : F :=
  observed w ⟨12+column.val,by have := column.isLt; omega⟩ limb
def query (w : Nat → F) (column : Fin 4) (piece : Fin 4) : Vector F 4 :=
  fixedQuery w ⟨18*column.val+piece.val,by have := column.isLt; have := piece.isLt; omega⟩
def pack (low high : F) : BitVec 32 := BitVec.append (BitVec.ofNat 16 high.val) (BitVec.ofNat 16 low.val)
def byte (w : Nat → F) (column : Fin 4) (piece : Fin 4) : BitVec 8 :=
  BitVec.ofNat 8 (w (275+46*column.val+piece.val+piece.val/2)).val
/-- Actual D chunks after the native first XOR and half-word swap. -/
def dAfter (w : Nat → F) (column : Fin 4) : BitVec 32 :=
  BitVec.append (BitVec.append (byte w column 1) (byte w column 0))
    (BitVec.append (byte w column 3) (byte w column 2))
/-- First A/D pair of each of the four column G calls. This is no full G/hash
    result or natural whole-word modular-addition claim for arbitrary controls. -/
structure RowEffects (w : Nat → F) : Prop where
  initial : Airbender.NativeWorkerInitial.RowEffects w
  carries : ∀ column : Fin 4, ∀ slot : Fin 4, (carryBit w column slot).val ≤ 1
  bounds : ∀ column : Fin 4, ∀ limb : Fin 2, (sumLimb w column limb).val < 65536 ∧ (dInput w column limb).val < 65536
  rotated : ∀ column : Fin 4, dAfter w column =
    (pack (dInput w column 0) (dInput w column 1) ^^^ pack (sumLimb w column 0) (sumLimb w column 1)).rotateRight 16
end Airbender.NativeWorkerFirstG
