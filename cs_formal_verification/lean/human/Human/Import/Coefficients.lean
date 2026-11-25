module
public import Human.Import.Schema
public import Human.Helpers.Core.CircuitField
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace Airbender.Artifact

/-- Choose a small signed representative of a decoded BabyBear residue.
    Its interpretation is equivalent to the canonical residue in characteristic p. -/
def signedCoefficient (c : Coefficient) : Int :=
  CircuitField.signedScalar babyBearModulus c.raw.val

end Airbender.Artifact
