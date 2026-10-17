import Airbender.Import.Json
import Airbender.Review.Helpers.Core.Field

namespace Airbender
open Lean

/-- Rust Mersenne31Field stores a non-Montgomery residue in 0..=p. -/
structure Coefficient where
  raw : BoundedNat (mersenne31Modulus + 1)
  deriving Repr

instance : FromJson Coefficient where
  fromJson? j := Coefficient.mk <$> fromJson? j

instance : ToJson Coefficient where
  toJson c := toJson c.raw

def Coefficient.canonical (c : Coefficient) : Nat := c.raw.val % mersenne31Modulus

end Airbender
