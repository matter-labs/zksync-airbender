import Airbender.Review.Helpers.Core.Field
import Airbender.Proofs.BabyBearPrimeCertificate
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

namespace Airbender

instance babyBearPrime : Fact (Nat.Prime babyBearModulus) := ⟨BabyBearPrimeCertificate.prime⟩

theorem babyBear_eq_of_natCast_zero {p : Nat} [Fact p.Prime]
    (characteristic : (babyBearModulus : ZMod p) = 0) : p = babyBearModulus := by
  have divisor : p ∣ babyBearModulus := (ZMod.natCast_eq_zero_iff _ _).mp characteristic
  exact ((Nat.dvd_prime babyBearPrime.out).mp divisor).resolve_left
    (Nat.Prime.ne_one (Fact.out : p.Prime))

end Airbender
