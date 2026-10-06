import Mathlib.Data.Nat.Basic

namespace Airbender.Arithmetic

/-- Canonical two-limb encodings are injective, for any limb base.
    Only the low limbs need bounds; the high limbs may be arbitrary naturals. -/
theorem two_limb_encoding_injective {base leftLo leftHi rightLo rightHi : Nat}
    (hl : leftLo < base) (hr : rightLo < base)
    (hv : leftLo + base * leftHi = rightLo + base * rightHi) :
    leftLo = rightLo ∧ leftHi = rightHi := by
  have hlo : leftLo = rightLo := by
    have hm := congrArg (fun n => n % base) hv
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr] using hm
  have hprod : base * leftHi = base * rightHi := by
    rw [hlo] at hv
    exact Nat.add_left_cancel hv
  exact ⟨hlo, Nat.eq_of_mul_eq_mul_left (by omega) hprod⟩

end Airbender.Arithmetic
