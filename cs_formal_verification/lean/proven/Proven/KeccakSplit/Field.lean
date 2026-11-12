module
public import Human.Helpers.Core.BabyBearPrime
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Airbender.Keccak.Split.Native.Proofs

/-- The claims' serialized inverse `256 · (-7864320) = 1` holds only in BabyBear. -/
theorem scale256_field {p : Nat} [Fact p.Prime]
    (inverse : 256 * (-7864320 : ZMod p) = 1) : p = babyBearModulus := by
  have characteristic : (babyBearModulus : ZMod p) = 0 := by
    unfold babyBearModulus
    linear_combination -inverse
  have divisor : p ∣ babyBearModulus := (ZMod.natCast_eq_zero_iff _ _).mp characteristic
  exact ((Nat.dvd_prime babyBearPrime.out).mp divisor).resolve_left
    (Nat.Prime.ne_one (Fact.out : p.Prime))

end Airbender.Keccak.Split.Native.Proofs
