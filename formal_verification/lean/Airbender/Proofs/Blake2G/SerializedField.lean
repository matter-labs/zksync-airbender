import Mathlib.Tactic.LinearCombination
import Airbender.Proofs.BabyBear

namespace Airbender.Blake2G.Proofs
set_option Elab.async false

/-- This serialized inverse belongs to BabyBear. A different field needs its
    own imported coefficients, even though the arithmetic lemmas are generic. -/
theorem serialized_field {p : Nat} [Fact p.Prime]
    (compatible : 64 * (-31457280 : ZMod p) = 1) : p = babyBearModulus := by
  have characteristic : (babyBearModulus : ZMod p) = 0 := by
    unfold babyBearModulus
    linear_combination -compatible
  have divisor : p ∣ babyBearModulus := (ZMod.natCast_eq_zero_iff _ _).mp characteristic
  exact ((Nat.dvd_prime babyBearPrime.out).mp divisor).resolve_left
    (Nat.Prime.ne_one (Fact.out : p.Prime))

end Airbender.Blake2G.Proofs
