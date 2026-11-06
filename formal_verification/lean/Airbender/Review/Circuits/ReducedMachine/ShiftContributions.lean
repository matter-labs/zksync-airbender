import Airbender.Review.Circuits.ReducedMachine.ShiftWrite
import Airbender.Review.Circuits.ReducedMachine.Tables.ShiftImplementation

namespace Airbender.ReducedMachine.Native

/-- Actual two-field contribution for the selected source-one limb. -/
def shiftContribution (w : Nat → ZMod mersenne31Modulus) (limb : Fin 2) :
    Vector (ZMod mersenne31Modulus) 2 :=
  if limb.val = 0 then shiftLowParts w else shiftHighParts w

end Airbender.ReducedMachine.Native
