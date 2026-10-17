import Airbender.Import.Mersenne31
import Mathlib.Data.ZMod.Basic

namespace Airbender.Artifact

def signedCoefficient (c : Coefficient) : Int :=
  let n := c.canonical
  if n ≤ mersenne31Modulus / 2 then n else (n : Int) - mersenne31Modulus

theorem signedCoefficient_mod (c : Coefficient) :
    signedCoefficient c % (mersenne31Modulus : Int) = c.canonical := by
  have bound : c.canonical < mersenne31Modulus := Nat.mod_lt _ (by decide)
  unfold signedCoefficient
  dsimp only
  split
  · exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast bound)
  · rw [Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod]
    exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast bound)

theorem signedCoefficient_cast {F : Type} [CommRing F] [CharP F mersenne31Modulus]
    (c : Coefficient) : (signedCoefficient c : F) = (c.canonical : F) := by
  rw [CharP.intCast_eq_intCast_mod F mersenne31Modulus (a := signedCoefficient c),
    signedCoefficient_mod, Int.cast_natCast]

theorem serialized_modulus_is_zero :
    (Coefficient.mk ⟨2147483647, by decide⟩).canonical = 0 := by decide

end Airbender.Artifact
