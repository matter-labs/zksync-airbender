import Airbender.Proofs.Tables.PackedWordBounds
namespace Airbender.Setup.Proofs.PackedDisjointSum
set_option warningAsError true

theorem disjoint_or (left right : Nat) (disjoint : left &&& right = 0) :
    left ||| right = left + right := by
  induction left using Nat.strong_induction_on generalizing right with
  | h left ih =>
    by_cases leftZero : left = 0
    · subst left; simp
    by_cases rightZero : right = 0
    · subst right; simp
    have halfDisjoint : left / 2 &&& right / 2 = 0 := by
      have projected := Nat.and_div_two_pow (a := left) (b := right) (n := 1)
      rw [disjoint] at projected
      exact projected.symm
    have smaller : left / 2 < left := Nat.div_lt_self (by omega) (by omega)
    have result := ih (left / 2) smaller (right / 2) halfDisjoint
    have leftParts := Nat.div_add_mod left 2
    have rightParts := Nat.div_add_mod right 2
    have leftMod := Nat.mod_lt left (show 0 < 2 by omega)
    have rightMod := Nat.mod_lt right (show 0 < 2 by omega)
    change Nat.bitwise Bool.and left right = 0 at disjoint
    rw [Nat.bitwise] at disjoint
    simp only [if_neg leftZero, if_neg rightZero] at disjoint
    change Nat.bitwise Bool.or left right = left + right
    rw [Nat.bitwise]
    simp only [if_neg leftZero, if_neg rightZero]
    change Nat.bitwise Bool.or (left / 2) (right / 2) = left / 2 + right / 2 at result
    by_cases leftOdd : left % 2 = 1 <;> by_cases rightOdd : right % 2 = 1
    all_goals simp only [leftOdd, rightOdd, decide_true, decide_false,
      Bool.true_and, Bool.false_and, Bool.true_or, Bool.false_or, Bool.false_eq_true,
      if_true, if_false] at disjoint ⊢
    all_goals rw [result]
    all_goals omega
end Airbender.Setup.Proofs.PackedDisjointSum
