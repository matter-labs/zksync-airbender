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

/-- The canonical representative of a field bit is at most one. -/
theorem boolean_val {p : Nat} {x : ZMod p} (h : x = 0 ∨ x = 1) : x.val ≤ 1 := by
  rcases h with h | h
  · simp [h]
  · rw [h, show (1 : ZMod p).val = 1 % p from by
      simpa only [Nat.cast_one] using ZMod.val_natCast p 1]
    exact Nat.mod_le 1 p

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

/-- A ranged subtraction and a carry bit classify a 16-bit limb against a
    threshold. Shared by the memory families' ROM/RAM selection. -/
theorem range_separator {p high threshold : Nat} [Fact p.Prime] (hp : 131072 < p)
    {residue flag : ZMod p} (highBound : high < 65536) (thresholdBound : threshold ≤ 65536)
    (residueBound : residue.val < 65536) (bit : flag = 0 ∨ flag = 1)
    (equation : residue + threshold = (high : ZMod p) + 65536 * flag) :
    flag = if high < threshold then 1 else 0 := by
  rcases bit with bit | bit
  · have field : ((residue.val + threshold : Nat) : ZMod p) = high := by
      simpa only [Nat.cast_add, ZMod.natCast_zmod_val, bit, mul_zero, add_zero] using equation
    have natural : residue.val + threshold = high :=
      bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega) field
    simp [bit, show ¬ high < threshold by omega]
  · have field : ((residue.val + threshold : Nat) : ZMod p) = high + 65536 := by
      simpa only [Nat.cast_add, ZMod.natCast_zmod_val, bit, mul_one] using equation
    have natural : residue.val + threshold = high + 65536 :=
      bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega) (by exact_mod_cast field)
    simp [bit, show high < threshold by omega]

end Airbender.Arithmetic
