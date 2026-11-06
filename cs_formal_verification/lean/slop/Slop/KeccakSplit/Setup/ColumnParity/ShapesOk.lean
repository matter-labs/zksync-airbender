import Slop.KeccakSplit.Setup.ColumnParity.Shapes
import Mathlib.Tactic.IntervalCases

/- Algebraic agreement of every listed long block with its row formula. -/

namespace Airbender.Keccak.Split.ColumnParity.SetupProofs

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
    simp only [col0Spec, spec0, nib, callAt, callIndex, Int.ofNat_eq_natCast, Nat.reducePow, pow_zero, Nat.div_one]
    split_ifs <;> omega

theorem col1_longs : ∀ p ∈ col1Longs, p.2.Ok col1Spec p.1 := by
  intro p hp
  simp only [col1Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl | rfl)
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    try intro j _hj
    simp only [col1Spec, spec1, nib, callAt, callIndex, Int.ofNat_eq_natCast, Nat.reducePow, pow_zero, Nat.div_one]
    split_ifs <;> omega

theorem col2_longs : ∀ p ∈ col2Longs, p.2.Ok col2Spec p.1 := by
  intro p hp
  simp only [col2Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with (⟨k, _hk, rfl⟩) | rfl
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    try intro j _hj
    simp only [col2Spec, spec2, nib, callAt, callIndex, Int.ofNat_eq_natCast, Nat.reducePow, pow_zero, Nat.div_one]
    split_ifs <;> omega

theorem col3_longs : ∀ p ∈ col3Longs, p.2.Ok col3Spec p.1 := by
  intro p hp
  simp only [col3Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with ((rfl) | ⟨k, _hk, rfl⟩) | rfl
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    simp only [col3Spec, spec3, nib, callAt, callIndex, Int.ofNat_eq_natCast, Nat.reducePow, pow_zero, Nat.div_one]
    split_ifs <;> omega

theorem col4_longs : ∀ p ∈ col4Longs, p.2.Ok col4Spec p.1 := by
  intro p hp
  simp only [col4Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with (((rfl | rfl)) | ⟨k, _hk, rfl⟩) | rfl
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    simp only [col4Spec, spec4, nib, callAt, callIndex, Int.ofNat_eq_natCast, Nat.reducePow, pow_zero, Nat.div_one]
    split_ifs <;> omega

theorem col5_longs : ∀ p ∈ col5Longs, p.2.Ok col5Spec p.1 := by
  intro p hp
  simp only [col5Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl)
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    simp only [col5Spec, spec5, nib, callAt, callIndex, Int.ofNat_eq_natCast, Nat.reducePow, pow_zero, Nat.div_one]
    split_ifs <;> omega

theorem col6_longs : ∀ p ∈ col6Longs, p.2.Ok col6Spec p.1 := by
  intro p hp
  simp only [col6Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl)
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    simp only [col6Spec, spec6, nib, callAt, callIndex, Int.ofNat_eq_natCast, Nat.reducePow, pow_zero, Nat.div_one]
    split_ifs <;> omega

theorem col7_longs : ∀ p ∈ col7Longs, p.2.Ok col7Spec p.1 := by
  intro p hp
  simp only [col7Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl | rfl)
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    simp only [col7Spec, spec7, nib, callAt, callIndex, Int.ofNat_eq_natCast, Nat.reducePow, pow_zero, Nat.div_one]
    split_ifs <;> omega


end Airbender.Keccak.Split.ColumnParity.SetupProofs
