module
public import Human.Helpers.Core.CircuitField
public import Mathlib.Tactic.LinearCombination

@[expose] public section
namespace Airbender.CircuitField
variable {p : Nat} [CircuitField p]

/-- Reading a coefficient via its canonical integer gives the same value as field multiplication. -/
theorem canonical_cast (raw : Nat) : (canonical p raw : ZMod p) = decode p raw := by
  simp [canonical, decode]

theorem signedScalar_cast (raw : Nat) :
    (signedScalar p raw : ZMod p) = (raw : ZMod p) * (montgomeryInverse p : ZMod p) := by
  dsimp only [signedScalar, canonical]
  split <;> simp

/-- The byte and timestamp denominators both divide p−1, so their inverse in the
    host field is obtained without storing a separate field-specific coefficient. -/
theorem invPow_mul (k : Nat) (hk : k ≤ 19) :
    -(negInvPow p k : ZMod p) * 2 ^ k = 1 := by
  have divides : 2 ^ k ∣ p - 1 := (pow_dvd_pow 2 hk).trans (twoAdicity (p := p))
  have natural : negInvPow p k * 2 ^ k + 1 = p := by
    rw [negInvPow, Nat.div_mul_cancel divides, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
  have h := congrArg (fun n : Nat => (n : ZMod p)) natural
  push_cast at h
  simp only [ZMod.natCast_self] at h
  linear_combination -h

end Airbender.CircuitField
