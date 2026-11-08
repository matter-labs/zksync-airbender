import Airbender.Review.Circuits.Blake2Worker.Control

namespace Airbender.NativeWorkerSchedule
open Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus
/-- Exact pinned native message schedules. This reference supplies no witness
    answers or assumption that a round mask is one-hot. -/
def sigma : Vector (Vector (Fin 16) 16) 10 := #v[
  #v[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
  #v[14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3],
  #v[11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4],
  #v[7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8],
  #v[9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13],
  #v[2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9],
  #v[12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11],
  #v[13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10],
  #v[6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5],
  #v[10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0]]

def inputBit (w : Nat → F) (slot : Fin 13) : Nat := (w 135).val / 2^slot.val % 2

def message (w : Nat → F) (word : Fin 16) (limb : Fin 2) : F := w (102+2*word.val+limb.val)
def state (w : Nat → F) (word : Fin 8) (limb : Fin 2) : F := w (4+4*word.val+limb.val)
/-- Actual compression input choice, with original message/state operands. -/
def input (w : Nat → F) (word : Fin 16) (limb : Fin 2) : F :=
  if inputBit w 2 = 0 then message w word limb else
  if h : word.val < 8 then
    if inputBit w 1 = 1 then message w word limb else state w ⟨word.val,by omega⟩ limb
  else if inputBit w 1 = 1 then state w ⟨word.val-8,by have := word.isLt; omega⟩ limb else message w ⟨word.val-8,by have := word.isLt; omega⟩ limb

def selected (w : Nat → F) (word : Fin 16) (limb : Fin 2) : F := w (236+2*word.val+limb.val)
/-- General Boolean weighted schedule, retaining zero and multiple round bits. -/
def scheduled (w : Nat → F) (word : Fin 16) (limb : Fin 2) : F :=
  ∑ round : Fin 10, (inputBit w ⟨3+round.val,by omega⟩ : F) * input w sigma[round][word] limb

def nextHigh (high : Nat) := high % 8 + 16 * (high / 8 % 512)

/-- Pointwise control/input/message-schedule consequences of the FULL native
    BODY. Zero/multiple round bits remain in the Boolean-weighted schedule.
    This does not assert a standard hash round, issued call or physical schedule.
    The old x12 low limb and every raw memory token remain in source acceptance. -/
structure RowEffects (w : Nat → F) : Prop where
  control : ControlEffects w
  flags : ∀ slot : Fin 13, w (138+slot.val) = (inputBit w slot : F)
  inputs : ∀ word : Fin 16, ∀ limb : Fin 2, w (204+2*word.val+limb.val) = input w word limb
  schedule : ∀ word : Fin 16, ∀ limb : Fin 2, selected w word limb = scheduled w word limb
  update : w 136 = 0 ∧ (w 137).val = nextHigh (w 135).val
end Airbender.NativeWorkerSchedule
