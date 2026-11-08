import Airbender.Review.Circuits.Blake2Worker.FirstG

namespace Airbender.NativeWorkerAddition
open Airbender.NativeWorkerSchedule Airbender.NativeWorkerInitial Airbender.NativeWorkerFirstG
abbrev F := ZMod mersenne31Modulus
/-- Natural weighted schedule with every original round bit, including zero and
    multiple bits. No one-hot schedule or u16 selected-message claim. -/
def selectedNatural (w : Nat → F) (word : Fin 16) (limb : Fin 2) : Nat :=
  ∑ round : Fin 10, inputBit w ⟨3+round.val,by omega⟩ * (input w sigma[round][word] limb).val
/-- Retain wide selected limbs before reduction modulo the RV32 word modulus. -/
def messageWord (w : Nat → F) (word : Fin 16) : BitVec 32 :=
  BitVec.ofNat 32 ((selected w word 0).val+65536*(selected w word 1).val)
def preGWord (w : Nat → F) (word : Fin 16) : BitVec 32 := pack (observed w word 0) (observed w word 1)
def aAfter (w : Nat → F) (column : Fin 4) : BitVec 32 := pack (sumLimb w column 0) (sumLimb w column 1)
/-- Initialized consequences on the same counted source. This covers first A/D
    pairs, not the remaining G operations, full hash or physical round schedule. -/
structure RowEffects (w : Nat → F) : Prop where
  prior : Airbender.NativeWorkerFirstG.RowEffects w
  initial : ∀ word : Fin 16, ∀ limb : Fin 2, (observed w word limb).val < 65536
  inputs : ∀ word : Fin 16, ∀ limb : Fin 2, (input w word limb).val < 65536
  selected : ∀ word : Fin 16, ∀ limb : Fin 2,
    (Airbender.NativeWorkerSchedule.selected w word limb).val = selectedNatural w word limb ∧ selectedNatural w word limb < 655360
  carries : ∀ column : Fin 4, ∀ limb : Fin 2, (carry w column limb).val ≤ 3
  added : ∀ column : Fin 4, aAfter w column =
    preGWord w ⟨column.val,by have := column.isLt; omega⟩ +
    preGWord w ⟨4+column.val,by have := column.isLt; omega⟩ +
    messageWord w ⟨2*column.val,by have := column.isLt; omega⟩
end Airbender.NativeWorkerAddition
