import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

namespace Airbender.Arithmetic

theorem boolean_nat {F : Type} [Field F] {x : F} (h : x * (x - 1) = 0) :
    ∃ n : Nat, n ≤ 1 ∧ x = (n : F) := by
  rcases mul_eq_zero.mp h with hz | ho
  · exact ⟨0, by omega, by simpa using hz⟩
  · exact ⟨1, by omega, by simpa using sub_eq_zero.mp ho⟩

/-- Recover a two-limb increment from a Boolean carry expression. The inverse
    premise is checked against each artifact's serialized coefficient. -/
theorem increment_carry {F : Type} [Field F] {inverse radix increment lo hi nextLo nextHi : F}
    (hinv : inverse * radix = 1)
    (boolean : (inverse * (lo + increment - nextLo)) *
      (inverse * (lo + increment - nextLo) - 1) = 0)
    (high : inverse * (lo + increment - nextLo) + hi - nextHi = 0) :
    ∃ c : Nat, c ≤ 1 ∧ lo + increment = nextLo + radix * c ∧ hi + c = nextHi := by
  obtain ⟨c, cb, hc⟩ := boolean_nat boolean
  refine ⟨c, cb, ?_, ?_⟩
  · have recovered : lo + increment - nextLo = radix * c := by
      calc
        _ = (inverse * radix) * (lo + increment - nextLo) := by rw [hinv]; ring
        _ = radix * (inverse * (lo + increment - nextLo)) := by ring
        _ = radix * c := by rw [hc]
    linear_combination recovered
  · rw [hc] at high
    linear_combination high

/-- Lift a field equality once both natural sums are strictly below the characteristic.
    Applicable to both small and large outer fields; no fixed modulus in this lemma. -/
theorem bounded_nat_eq {F : Type} [CommRing F] {p a b : Nat} [CharP F p]
    (ha : a < p) (hb : b < p) (h : (a : F) = (b : F)) : a = b :=
  ((CharP.natCast_eq_natCast F p).mp h).eq_of_lt_of_lt ha hb

end Airbender.Arithmetic
