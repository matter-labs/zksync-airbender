import Airbender.Review.Circuits.Blake2Worker.NativeArtifact
import Airbender.Proofs.Mersenne31

namespace Airbender.Blake2Worker.Native

def controlHigh (w : Nat → ZMod mersenne31Modulus) : Nat := (w 135).val

def nextControlHigh (w : Nat → ZMod mersenne31Modulus) : Nat := (w 137).val

/-- Local native x12 observations only. Thirteen Boolean flags do not establish
    a valid round schedule, a nonzero/one-hot mask, or a fulfilled request. -/
structure ControlEffects (w : Nat → ZMod mersenne31Modulus) : Prop where
  flags : ∀ slot : Fin 13, (w (138+slot.val)).val ≤ 1
  inputBounded : controlHigh w < 8192
  outputBounded : nextControlHigh w < 8192
  lowCleared : w 136 = 0

end Airbender.Blake2Worker.Native
