import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Airbender.Arithmetic

theorem boolean_nat {F : Type} [Field F] {x : F} (h : x * (x - 1) = 0) :
    ∃ n : Nat, n ≤ 1 ∧ x = (n : F) := by
  rcases mul_eq_zero.mp h with hz | ho
  · exact ⟨0, by omega, by simpa using hz⟩
  · exact ⟨1, by omega, by simpa using sub_eq_zero.mp ho⟩

/-- Lift a field equality once both natural sums are strictly below the characteristic.
    Applicable to both small and large outer fields; no fixed modulus in this lemma. -/
theorem bounded_nat_eq {F : Type} [CommRing F] {p a b : Nat} [CharP F p]
    (ha : a < p) (hb : b < p) (h : (a : F) = (b : F)) : a = b :=
  ((CharP.natCast_eq_natCast F p).mp h).eq_of_lt_of_lt ha hb

end Airbender.Arithmetic
