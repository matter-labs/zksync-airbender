module
public import Human.Import.Schema
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace Airbender.Artifact

/-- Choose a small signed representative of a decoded BabyBear residue.
    Its interpretation is equivalent to the canonical residue in characteristic p. -/
def signedCoefficient (c : Coefficient) : Int :=
  let n := c.canonical.val
  if n ≤ babyBearModulus / 2 then n else (n : Int) - babyBearModulus

end Airbender.Artifact
