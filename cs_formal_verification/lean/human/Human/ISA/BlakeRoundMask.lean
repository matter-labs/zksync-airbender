module
public import Human.ISA.Blake2s

@[expose] public section
namespace RV.Delegation
open Spec

/-- Native control bits select any subset of the ten BLAKE2s message schedules. -/
def roundMaskBit (control : Word) (round : Fin 10) : Bool := control.getLsbD (19 + round.val)

/-- The native schedule adds all selected message words modulo 32 bits. -/
def maskedRoundMessage (control : Word) (message : Vector Word 16) : Vector Word 16 :=
  Vector.ofFn fun position => BitVec.ofNat 32
    ((List.finRange 10).map fun round =>
      if roundMaskBit control round then (message[SIGMA round position]).toNat else 0).sum

/-- Round seven has priority when both final-round bits are set. -/
def maskedRoundFinal (control : Word) : Bool :=
  if roundMaskBit control 6 then control.getLsbD 16 else roundMaskBit control 9

end RV.Delegation
