module
public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section
namespace Airbender

/-- Base field of the L1 wrap circuit (`field/src/proth120.rs`). -/
def proth120Modulus : Nat := 7 * 2 ^ 120 + 1

instance proth120Prime : Fact proth120Modulus.Prime := ⟨by
  apply lucas_primality _ (3 : ZMod proth120Modulus) (by decide +kernel)
  intro q prime divides
  change q ∣ 7 * 2 ^ 120 at divides
  rcases prime.dvd_mul.mp divides with h | h
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq prime (by decide : Nat.Prime 7)).mp h
    decide +kernel
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq prime Nat.prime_two).mp (prime.dvd_of_dvd_pow h)
    decide +kernel⟩

end Airbender
