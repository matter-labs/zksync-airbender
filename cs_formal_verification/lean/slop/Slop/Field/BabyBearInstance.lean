module
public import Human.Helpers.Core.BabyBearPrime
public import Mathlib.Tactic.LinearCombination

/-! The claims' field premises pin BabyBear: an inverse premise `(-a : ZMod p) * b = 1` (or `b * (-a) = 1`) with
`a * b = babyBearModulus - 1` says `p ∣ babyBearModulus`, so a prime `p` is `babyBearModulus`. `babybear_instance h`
proves a claim stated at BabyBear from a proof `h` of the same statement for every prime `p` with those premises;
`eq_babyBear_of_cast_eq_zero` gives the converse (test/Checks/Restatements.lean). -/

@[expose] public section

namespace Airbender.Field

/-- A prime dividing the BabyBear modulus is the BabyBear modulus. -/
theorem eq_babyBear_of_cast_eq_zero {p : Nat} [hp : Fact p.Prime]
    (h : ((babyBearModulus : Nat) : ZMod p) = 0) : p = babyBearModulus := by
  have dvd : p ∣ babyBearModulus := (ZMod.natCast_eq_zero_iff _ _).mp h
  exact (Nat.prime_dvd_prime_iff_eq hp.out babyBearPrime.out).mp dvd

end Airbender.Field

/-- Close a BabyBear claim from a proof `h` of its generic-prime form `∀ {p} [Fact p.Prime], premises → …`:
    instantiate `p := babyBearModulus` and discharge its one to five numeric premises by `decide`. -/
macro "babybear_instance " h:term : tactic => `(tactic| first
  | exact $h (p := Airbender.babyBearModulus) (by decide)
  | exact $h (p := Airbender.babyBearModulus) (by decide) (by decide)
  | exact $h (p := Airbender.babyBearModulus) (by decide) (by decide) (by decide)
  | exact $h (p := Airbender.babyBearModulus) (by decide) (by decide) (by decide) (by decide)
  | exact $h (p := Airbender.babyBearModulus) (by decide) (by decide) (by decide) (by decide) (by decide))
