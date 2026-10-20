import Human.Helpers.Core.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

namespace Airbender

set_option maxRecDepth 100000 in
/-- The BabyBear modulus is prime: the field the BabyBear statements are stated over. -/
instance babyBearPrime : Fact (Nat.Prime babyBearModulus) := ⟨by norm_num [babyBearModulus]⟩

end Airbender
