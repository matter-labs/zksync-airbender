import Airbender.Review.Circuits.JumpBranchSlt.Artifact

namespace Airbender.JumpBranchSlt
open Verification

/-- The native control lookup's four-bit key, assembled from witness columns. -/
def controlBits (w : Nat → ZMod p) : ZMod p :=
  12 + w 28 + 2 * w 29 + (-4) * w 31 + (-8) * w 33

/-- Exact fixed-lookup effects on native observables. Instruction selection,
    initialized reads and original Sail PC/register soundness are separate. -/
structure FixedEffects (w : Nat → ZMod mersenne31Modulus) : Prop where
  bitsBound : (controlBits w).val < 16
  funct3Bound : (w 11).val < 8
  control : w 35 = if controlFlag (controlBits w).val (w 11).val then 1 else 0
  cleanupBound : (w 42).val < 65536
  bit1 : w 47 = ((w 42).val / 2 % 2 : Nat)
  cleaned : w 48 = (4 * ((w 42).val / 4) : Nat)

end Airbender.JumpBranchSlt
