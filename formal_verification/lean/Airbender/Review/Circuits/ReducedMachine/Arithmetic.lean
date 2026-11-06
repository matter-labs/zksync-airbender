import Airbender.Review.Circuits.ReducedMachine.ShiftWrite

namespace Airbender.ReducedMachine.Native

/-- Ordinary arithmetic profiles in the actual monolithic reduced decoder.
    These masks are distinct from the standalone eight-bit arithmetic family. -/
inductive ArithmeticMode
  | add | addi | sub | lui | auipc
  deriving DecidableEq

def ArithmeticMode.mask : ArithmeticMode → Nat
  | .add => 11 | .addi => 9 | .sub => 8195 | .lui => 513 | .auipc => 17

def ArithmeticMode.useRegister : ArithmeticMode → Bool
  | .add | .sub => true | _ => false

/-- Native candidate fields before the original rd/x0 mask. -/
def arithmeticCandidate (w : Nat → ZMod mersenne31Modulus) : Vector (ZMod mersenne31Modulus) 2 :=
  #v[w 116,w 117]

end Airbender.ReducedMachine.Native
