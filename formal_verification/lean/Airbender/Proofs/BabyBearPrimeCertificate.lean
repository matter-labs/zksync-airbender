import Airbender.Review.Helpers.Core.Field
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
namespace Airbender.BabyBearPrimeCertificate

-- A Lucas certificate avoids the deeply nested trial-division proof produced
-- by norm_num for this 31-bit prime. Each modular power is checked separately;
-- the only prime factors of the group order are 2, 3 and 5.
set_option warningAsError true
private theorem full_power : (31 : ZMod 2013265921) ^ 2013265920 = 1 := by
  reduce_mod_char
private theorem half_power : (31 : ZMod 2013265921) ^ 1006632960 ≠ 1 := by
  reduce_mod_char
  decide +kernel
private theorem third_power : (31 : ZMod 2013265921) ^ 671088640 ≠ 1 := by
  reduce_mod_char
  decide +kernel
private theorem fifth_power : (31 : ZMod 2013265921) ^ 402653184 ≠ 1 := by
  reduce_mod_char
  decide +kernel
private theorem prime_factors {q : Nat} (hq : q.Prime) (hd : q ∣ 2013265920) :
    q = 2 ∨ q = 3 ∨ q = 5 := by
  have factorization : 2013265920 = (2 ^ 27 * 3) * 5 := by decide +kernel
  rw [factorization] at hd
  rcases hq.dvd_mul.mp hd with hd | hd
  · rcases hq.dvd_mul.mp hd with hd | hd
    · have h2 : q ∣ 2 := hq.dvd_of_dvd_pow hd
      exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left hq.ne_one)
    · exact Or.inr (Or.inl ((Nat.dvd_prime (by decide +kernel : Nat.Prime 3)).mp hd
        |>.resolve_left hq.ne_one))
  · exact Or.inr (Or.inr ((Nat.dvd_prime (by decide +kernel : Nat.Prime 5)).mp hd
      |>.resolve_left hq.ne_one))
theorem prime : Nat.Prime babyBearModulus := by
  change Nat.Prime 2013265921
  apply lucas_primality 2013265921 (31 : ZMod 2013265921) full_power
  intro q hq hd
  rcases prime_factors hq hd with rfl | rfl | rfl
  · exact half_power
  · exact third_power
  · exact fifth_power
end Airbender.BabyBearPrimeCertificate
