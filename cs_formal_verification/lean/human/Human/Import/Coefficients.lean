import Human.Import.Schema
import Mathlib.Data.ZMod.Basic

namespace Airbender.Artifact

/-- Choose a small signed representative of a decoded BabyBear residue.
    Its interpretation is equivalent to the canonical residue in characteristic p. -/
def signedCoefficient (c : Coefficient) : Int :=
  let n := c.canonical.val
  if n ≤ babyBearModulus / 2 then n else (n : Int) - babyBearModulus

theorem signedCoefficient_mod (c : Coefficient) :
    signedCoefficient c % (babyBearModulus : Int) = c.canonical.val := by
  have hb := c.canonical.isLt
  unfold signedCoefficient
  dsimp only
  split
  · exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast hb)
  · rw [Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod]
    exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast hb)

theorem signedCoefficient_cast {F : Type} [CommRing F] [CharP F babyBearModulus]
    (c : Coefficient) : (signedCoefficient c : F) = (c.canonical.val : F) := by
  rw [CharP.intCast_eq_intCast_mod F babyBearModulus (a := signedCoefficient c),
    signedCoefficient_mod, Int.cast_natCast]

end Airbender.Artifact
