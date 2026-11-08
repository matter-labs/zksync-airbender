import Airbender.Review.Circuits.Blake2Worker.ExtendedOutput

namespace Airbender.NativeWorkerFinalization
open Airbender.NativeWorkerFirstG
abbrev F := ZMod mersenne31Modulus
/-- Actual first-eight-state write values; all native ports/times stay separate. -/
def writeLimb (w : Nat → F) (word : Fin 8) (limb : Fin 2) : F := w (6+4*word.val+limb.val)
def writeWord (w : Nat → F) (word : Fin 8) : BitVec 32 := pack (writeLimb w word 0) (writeLimb w word 1)
def readWord (w : Nat → F) (word : Fin 8) : BitVec 32 :=
  pack (Airbender.NativeWorkerSchedule.state w word 0) (Airbender.NativeWorkerSchedule.state w word 1)
def baseWord (w : Nat → F) (word : Fin 8) : BitVec 32 :=
  pack (Airbender.NativeWorkerInitial.finalBase w word 0) (Airbender.NativeWorkerInitial.finalBase w word 1)
/-- Native reduce/round flags, including arbitrary zero/multiple round masks. -/
def performFinal (w : Nat → F) : Bool := decide (Airbender.NativeWorkerSchedule.inputBit w 12 = 1 ∨
  (Airbender.NativeWorkerSchedule.inputBit w 0 = 1 ∧ Airbender.NativeWorkerSchedule.inputBit w 9 = 1))
def xorResult (w : Nat → F) (word : Fin 8) : BitVec 32 :=
  (baseWord w word ^^^ Airbender.NativeWorkerExtendedOutput.writeWord w ⟨word.val,by have := word.isLt; omega⟩) ^^^
    Airbender.NativeWorkerExtendedOutput.writeWord w ⟨8+word.val,by have := word.isLt; omega⟩
structure LocalEffects (w : Nat → F) : Prop where
  selector : w 152 = if performFinal w then 1 else 0
  finalized : ∀ word : Fin 8, writeWord w word = if performFinal w then xorResult w word else readWord w word
structure RowEffects (w : Nat → F) : Prop where
  prior : Airbender.NativeWorkerExtendedOutput.RowEffects w
  selector : w 152 = if performFinal w then 1 else 0
  finalized : ∀ word : Fin 8, writeWord w word = if performFinal w then xorResult w word else readWord w word
end Airbender.NativeWorkerFinalization
