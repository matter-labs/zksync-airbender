import Slop.KeccakSplit.Setup.ThetaRho.Shapes
import Mathlib.Tactic.IntervalCases

/- Algebraic agreement of every listed long block with its row formula. -/

namespace Airbender.Keccak.Split.ThetaRho.SetupProofs

open Airbender.Import.Setup.Proofs Airbender.Keccak.Split.SetupProofs

set_option warningAsError true
set_option linter.unusedSimpArgs false

theorem col0_longs : ∀ p ∈ col0Longs, p.2.Ok col0Spec p.1 := by
  intro p hp
  simp only [col0Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl | rfl)
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    try intro j _hj
    simp only [col0Spec, spec0, callAt, ctl, slt, flag, splitA, splitB, splitS, callIndex, Int.ofNat_eq_natCast]
    split_ifs <;> omega

theorem col1_longs : ∀ p ∈ col1Longs, p.2.Ok col1Spec p.1 := by
  intro p hp
  simp only [col1Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with ((rfl) | ⟨k, _hk, rfl⟩) | rfl
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    try intro j _hj
    simp only [col1Spec, spec1, callAt, ctl, slt, flag, splitA, splitB, splitS, callIndex, Int.ofNat_eq_natCast]
    split_ifs <;> omega

theorem col2_longs : ∀ p ∈ col2Longs, p.2.Ok col2Spec p.1 := by
  intro p hp
  simp only [col2Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with (⟨k, _hk, rfl⟩) | rfl
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    simp only [col2Spec, spec2, callAt, ctl, slt, flag, splitA, splitB, splitS, callIndex, Int.ofNat_eq_natCast]
    split_ifs <;> omega

theorem col3_longs : ∀ p ∈ col3Longs, p.2.Ok col3Spec p.1 := by
  intro p hp
  simp only [col3Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · simp only [Shape.Ok]
    intro i _hi
    by_cases h : i = 65536
    · subst h; decide
    · simp only [col3Spec, spec3, callAt, ctl, slt, flag, splitA, splitB, splitS, callIndex, Int.ofNat_eq_natCast]
      split_ifs <;> omega
  · simp only [Shape.Ok]
    intro i _hi
    simp only [col3Spec, spec3, callAt, ctl, slt, flag, splitA, splitB, splitS, callIndex, Int.ofNat_eq_natCast]
    split_ifs <;> omega

/-- The XOR-and-split high fragment is zero in its first 65664 rows (shift 0, or shift 1
    with second byte 0 and first byte below 128); below row 65536 the column is zero. -/
theorem col4_head (n : Nat) (hn : n < 131200) : spec4 n = 0 := by
  unfold spec4
  by_cases h1 : n < 65536
  · rw [ite_eq_left h1]
  rw [ite_eq_right h1, ite_eq_left (by omega : n < 589824)]
  have ha : splitA n < 256 := Nat.mod_lt _ (by decide)
  have hb : splitB n < 256 := Nat.mod_lt _ (by decide)
  have hx : splitA n ^^^ splitB n < 256 := Nat.xor_lt_two_pow (n := 8) ha hb
  by_cases hs : splitS n = 0
  · rw [hs]
    exact Nat.div_eq_of_lt hx
  · have hs1 : splitS n = 1 := by simp only [splitS] at hs ⊢; omega
    have hb0 : splitB n = 0 := by simp only [splitB, splitS] at hs ⊢; omega
    have ha128 : splitA n < 128 := by simp only [splitA, splitS] at hs ⊢; omega
    rw [hs1, hb0, Nat.xor_zero]
    exact Nat.div_eq_of_lt ha128

theorem col4_longs : ∀ p ∈ col4Longs, p.2.Ok col4Spec p.1 := by
  intro p hp
  simp only [col4Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · simp only [Shape.Ok]
    intro i hi
    rw [col4Spec, Nat.zero_add, col4_head i hi]
    simp
  · simp only [Shape.Ok]
    intro i _hi
    simp only [col4Spec, spec4, callAt, ctl, slt, flag, splitA, splitB, splitS, callIndex, Int.ofNat_eq_natCast]
    split_ifs <;> omega

theorem col5_longs : ∀ p ∈ col5Longs, p.2.Ok col5Spec p.1 := by
  intro p hp
  simp only [col5Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · simp only [Shape.Ok]
    intro i hi
    by_cases h : i < 589824
    · simp only [col5Spec, spec5, callAt, ctl, slt, flag, splitA, splitB, splitS, callIndex, Int.ofNat_eq_natCast]
      split_ifs <;> omega
    · obtain ⟨t, rfl⟩ : ∃ t, i = 589824 + t := ⟨i - 589824, by omega⟩
      have ht : t < 3 := by omega
      interval_cases t <;> decide
  · simp only [Shape.Ok]
    intro i _hi
    simp only [col5Spec, spec5, callAt, ctl, slt, flag, splitA, splitB, splitS, callIndex, Int.ofNat_eq_natCast]
    split_ifs <;> omega

theorem col6_longs : ∀ p ∈ col6Longs, p.2.Ok col6Spec p.1 := by
  intro p hp
  simp only [col6Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · simp only [Shape.Ok]
    intro i hi
    by_cases h : i < 589824
    · simp only [col6Spec, spec6, callAt, ctl, slt, flag, splitA, splitB, splitS, callIndex, Int.ofNat_eq_natCast]
      split_ifs <;> omega
    · obtain ⟨t, rfl⟩ : ∃ t, i = 589824 + t := ⟨i - 589824, by omega⟩
      have ht : t < 4 := by omega
      interval_cases t <;> decide
  · simp only [Shape.Ok]
    intro i _hi
    simp only [col6Spec, spec6, callAt, ctl, slt, flag, splitA, splitB, splitS, callIndex, Int.ofNat_eq_natCast]
    split_ifs <;> omega

theorem col7_longs : ∀ p ∈ col7Longs, p.2.Ok col7Spec p.1 := by
  intro p hp
  simp only [col7Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · simp only [Shape.Ok]
    intro i hi
    by_cases h : i < 589824
    · simp only [col7Spec, spec7, callAt, ctl, slt, flag, splitA, splitB, splitS, callIndex, Int.ofNat_eq_natCast]
      split_ifs <;> omega
    · obtain ⟨t, rfl⟩ : ∃ t, i = 589824 + t := ⟨i - 589824, by omega⟩
      have ht : t < 5 := by omega
      interval_cases t <;> decide
  · simp only [Shape.Ok]
    intro i _hi
    simp only [col7Spec, spec7, callAt, ctl, slt, flag, splitA, splitB, splitS, callIndex, Int.ofNat_eq_natCast]
    split_ifs <;> omega

theorem col8_longs : ∀ p ∈ col8Longs, p.2.Ok col8Spec p.1 := by
  intro p hp
  simp only [col8Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl | rfl)
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    simp only [col8Spec, spec8, callAt, ctl, slt, flag, splitA, splitB, splitS, callIndex, Int.ofNat_eq_natCast]
    split_ifs <;> omega


end Airbender.Keccak.Split.ThetaRho.SetupProofs
