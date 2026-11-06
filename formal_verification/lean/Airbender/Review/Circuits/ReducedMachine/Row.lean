import Airbender.Review.Circuits.ReducedMachine.NativeArtifact
import Airbender.Proofs.Mersenne31

namespace Airbender.ReducedMachine.Native

/-- Native reduced decoder's three supported shift variants. -/
inductive ShiftMode
  | left | right | arithmetic
  deriving DecidableEq

/-- Packed native decoder output: update-rd, optional rs2, shift major flag,
    and the original right/arithmetic minor flags. Public decoding is separate. -/
def ShiftMode.mask (mode : ShiftMode) (useRegister : Bool) : Nat :=
  4097 + (if useRegister then 2 else 0) +
    (match mode with | .left => 0 | .right => 65536 | .arithmetic => 98304)

/-- Actual routed source-two limbs, before interpreting initialized memory. -/
def source2 (w : Nat → ZMod mersenne31Modulus) : Vector (ZMod mersenne31Modulus) 2 :=
  #v[w 47,w 48]

def shiftAmount (w : Nat → ZMod mersenne31Modulus) : ZMod mersenne31Modulus := w 64

def lookupSelectors (w : Nat → ZMod mersenne31Modulus) : Vector (ZMod mersenne31Modulus) 4 :=
  #v[w 103,w 107,w 111,w 115]

end Airbender.ReducedMachine.Native
