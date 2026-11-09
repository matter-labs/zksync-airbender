import Airbender.Review.Trace.Families.ReducedMachine.SparseMain
import Airbender.Review.Trace.Families.ReducedMachine.InactiveGlobal

namespace Airbender.NativeWorkerSeed
open Airbender.ReducedMachine
abbrev F := ZMod mersenne31Modulus

/-- Retain every scalar/decoder/public observation around this SAME main.
    This constructs observations; it does not transfer any acceptance. -/
def withMain {R : Type} [Field R] (main : NativeMainArguments.Proof R) (proof : Airbender.NativeMainDecoder.Proof R) :
    Airbender.NativeMainDecoder.Proof R :=
  { proof with initialization := { proof.initialization with main := main } }

end Airbender.NativeWorkerSeed
