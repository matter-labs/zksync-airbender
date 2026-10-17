import Airbender.Review.Helpers.Core.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

namespace Airbender

instance mersenne31Prime : Fact (Nat.Prime mersenne31Modulus) :=
  ⟨by norm_num [mersenne31Modulus]⟩

end Airbender
