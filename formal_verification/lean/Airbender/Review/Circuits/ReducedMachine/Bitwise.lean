import Airbender.Review.Circuits.ReducedMachine.ArithmeticResult
import Airbender.Review.Helpers.Tables.Binary

namespace Airbender.ReducedMachine.Native
open Arithmetic Verification

/-- Actual reduced header and BINOP_COMMON_KEY bit; unlike split-family masks. -/
def bitwiseMask (useRegister : Bool) : Nat := 33 + if useRegister then 2 else 0

/-- Four actual native byte triples before architectural word reconstruction. -/
def bitwiseBytes (w : Nat → ZMod mersenne31Modulus) : Vector (Vector (ZMod mersenne31Modulus) 3) 4 :=
  #v[#v[w 55,w 58,w 64],#v[w 104,w 105,w 65],
    #v[w 108,w 109,w 66],#v[w 57,w 60,w 67]]

end Airbender.ReducedMachine.Native
