module
public import Human.Helpers.Core.Field
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace Airbender

set_option maxRecDepth 100000 in
/-- The BabyBear modulus is prime: the field the BabyBear statements are stated over. -/
instance babyBearPrime : Fact (Nat.Prime babyBearModulus) := ⟨by norm_num [babyBearModulus]⟩

end Airbender
