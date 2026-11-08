import Airbender.Review.Circuits.Blake2Worker.MemoryKeys
import Airbender.Review.Circuits.Blake2Worker.Finalization

namespace Airbender.NativeWorkerTransition
open Airbender.NativeWorkerFirstG (pack)
abbrev F := ZMod mersenne31Modulus
/-- Pure reference inputs: actual read limbs only. Both x12 fields are retained;
    the native transition uses the high field's thirteen control bits. -/
structure Input where
  controlLow : F
  controlHigh : Nat
  state : Fin 8 → Fin 2 → F
  extended : Fin 16 → Fin 2 → F
  message : Fin 16 → Fin 2 → F
def bit (i : Input) (slot : Fin 13) : Nat := i.controlHigh / 2^slot.val % 2
def baseLimb (i : Input) (word : Fin 8) (limb : Fin 2) : F :=
  if bit i 2 = 0 then i.state word limb else
    Airbender.NativeWorkerInitial.limbOf (Airbender.NativeWorkerInitial.configuredIV word) limb
def initialLimb (i : Input) (word : Fin 16) (limb : Fin 2) : F :=
  if bit i 3 = 0 then i.extended word limb else
  if h : word.val < 8 then baseLimb i ⟨word.val,h⟩ limb else
  if word.val = 12 ∨ word.val = 14 then
    if bit i 2 = 0 then i.extended word limb else
      Airbender.NativeWorkerInitial.limbOf (Airbender.NativeWorkerInitial.compressionIV word) limb
  else Airbender.NativeWorkerInitial.limbOf Airbender.NativeWorkerInitial.iv[(⟨word.val%8,by omega⟩ : Fin 8)] limb
def inputLimb (i : Input) (word : Fin 16) (limb : Fin 2) : F :=
  if bit i 2 = 0 then i.message word limb else
  if h : word.val < 8 then
    if bit i 1 = 1 then i.message word limb else i.state ⟨word.val,h⟩ limb
  else if bit i 1 = 1 then i.state ⟨word.val-8,by have := word.isLt; omega⟩ limb
  else i.message ⟨word.val-8,by have := word.isLt; omega⟩ limb
/-- Natural weighted limbs retain low carry before reduction modulo2^32.
    All ten bits participate; this is not a one-hot round precondition. -/
def selectedLimb (i : Input) (word : Fin 16) (limb : Fin 2) : Nat :=
  ∑ round : Fin 10, bit i ⟨3+round.val,by omega⟩ * (inputLimb i Airbender.NativeWorkerSchedule.sigma[round][word] limb).val
def initialWord (i : Input) (word : Fin 16) : BitVec 32 := pack (initialLimb i word 0) (initialLimb i word 1)
def selectedWord (i : Input) (word : Fin 16) : BitVec 32 :=
  BitVec.ofNat 32 (selectedLimb i word 0+65536*selectedLimb i word 1)
def column (i : Input) (c : Fin 4) : Vector (BitVec 32) 4 :=
  Airbender.NativeWorkerSecondCB.g
    (initialWord i ⟨c.val,by omega⟩) (initialWord i ⟨4+c.val,by have := c.isLt; omega⟩)
    (initialWord i ⟨8+c.val,by have := c.isLt; omega⟩) (initialWord i ⟨12+c.val,by have := c.isLt; omega⟩)
    (selectedWord i ⟨2*c.val,by have := c.isLt; omega⟩) (selectedWord i ⟨2*c.val+1,by have := c.isLt; omega⟩)
def routed (i : Input) (d c : Fin 4) : BitVec 32 :=
  (column i (Airbender.NativeWorkerDiagonalFirst.sourceColumn d c))[c]
def diagonal (i : Input) (d : Fin 4) : Vector (BitVec 32) 4 :=
  Airbender.NativeWorkerSecondCB.g (routed i d 0) (routed i d 1) (routed i d 2) (routed i d 3)
    (selectedWord i ⟨8+2*d.val,by have := d.isLt; omega⟩) (selectedWord i ⟨9+2*d.val,by have := d.isLt; omega⟩)
def extendedWord (i : Input) (word : Fin 16) : BitVec 32 :=
  (diagonal i (Airbender.NativeWorkerExtendedOutput.diagonalOf word))[Airbender.NativeWorkerExtendedOutput.componentOf word]
def performFinal (i : Input) : Bool := decide (bit i 12 = 1 ∨ (bit i 0 = 1 ∧ bit i 9 = 1))
def stateWord (i : Input) (word : Fin 8) : BitVec 32 :=
  if performFinal i then
    (pack (baseLimb i word 0) (baseLimb i word 1) ^^^ extendedWord i ⟨word.val,by have := word.isLt; omega⟩) ^^^
      extendedWord i ⟨8+word.val,by have := word.isLt; omega⟩
  else pack (i.state word 0) (i.state word 1)
structure Output where
  state : Fin 8 → BitVec 32
  extended : Fin 16 → BitVec 32
  controlLow : Nat
  controlHigh : Nat
/-- One complete native weighted-mask transition; no supplied witness intermediates
    or writes, and no assertion of a physical sequence or standard scheduled hash. -/
def transition (i : Input) : Output :=
  ⟨stateWord i,extendedWord i,0,Airbender.NativeWorkerSchedule.nextHigh i.controlHigh⟩
def readInput (w : Nat → F) : Input :=
  ⟨w 134,(w 135).val,Airbender.NativeWorkerSchedule.state w,
    Airbender.NativeWorkerInitial.oldExtended w,Airbender.NativeWorkerSchedule.message w⟩
def observed (w : Nat → F) : Output :=
  ⟨(fun word => pack
      (Airbender.Blake2Worker.Native.keyValue w ⟨1+word.val,by have := word.isLt; omega⟩ true)[(0 : Fin 2)]
      (Airbender.Blake2Worker.Native.keyValue w ⟨1+word.val,by have := word.isLt; omega⟩ true)[(1 : Fin 2)]),
    (fun word => pack
      (Airbender.Blake2Worker.Native.keyValue w ⟨9+word.val,by have := word.isLt; omega⟩ true)[(0 : Fin 2)]
      (Airbender.Blake2Worker.Native.keyValue w ⟨9+word.val,by have := word.isLt; omega⟩ true)[(1 : Fin 2)]),
    (Airbender.Blake2Worker.Native.keyValue w 42 true)[(0 : Fin 2)].val,
    (Airbender.Blake2Worker.Native.keyValue w 42 true)[(1 : Fin 2)].val⟩
structure RowEffects (w : Nat → F) : Prop where
  prior : Airbender.NativeWorkerFinalization.RowEffects w
  result : observed w = transition (readInput w)
end Airbender.NativeWorkerTransition
