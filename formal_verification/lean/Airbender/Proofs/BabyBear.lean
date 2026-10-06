import Airbender.Review.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

namespace Airbender

instance babyBearPrime : Fact (Nat.Prime babyBearModulus) := ⟨by norm_num [babyBearModulus]⟩

end Airbender
