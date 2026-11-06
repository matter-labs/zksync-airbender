import Slop.KeccakSplit.Setup.Chi5.Shapes
import Mathlib.Tactic.IntervalCases

/- Algebraic agreement of every listed long block with its row formula. -/

namespace Airbender.Keccak.Split.Chi5.SetupProofs

open Airbender.Import.Setup.Proofs Airbender.Keccak.Split.SetupProofs

set_option warningAsError true
set_option linter.unusedSimpArgs false

theorem col0_longs : ∀ p ∈ col0Longs, p.2.Ok col0Spec p.1 := by
  intro p hp
  simp only [col0Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl)
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    try intro j _hj
    simp only [col0Spec, spec0, nib, chiOut, callAt, ctl, callIndex, Int.ofNat_eq_natCast, Nat.reducePow, pow_zero, Nat.div_one]
    split_ifs <;> omega

theorem col1_longs : ∀ p ∈ col1Longs, p.2.Ok col1Spec p.1 := by
  intro p hp
  simp only [col1Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl)
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    try intro j _hj
    simp only [col1Spec, spec1, nib, chiOut, callAt, ctl, callIndex, Int.ofNat_eq_natCast, Nat.reducePow, pow_zero, Nat.div_one]
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
    simp only [col2Spec, spec2, nib, chiOut, callAt, ctl, callIndex, Int.ofNat_eq_natCast, Nat.reducePow, pow_zero, Nat.div_one]
    split_ifs <;> omega

theorem col3_longs : ∀ p ∈ col3Longs, p.2.Ok col3Spec p.1 := by
  intro p hp
  simp only [col3Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with (⟨k, _hk, rfl⟩) | rfl
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    simp only [col3Spec, spec3, nib, chiOut, callAt, ctl, callIndex, Int.ofNat_eq_natCast, Nat.reducePow, pow_zero, Nat.div_one]
    split_ifs <;> omega

theorem col4_longs : ∀ p ∈ col4Longs, p.2.Ok col4Spec p.1 := by
  intro p hp
  simp only [col4Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with (⟨k, _hk, rfl⟩) | rfl
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    simp only [col4Spec, spec4, nib, chiOut, callAt, ctl, callIndex, Int.ofNat_eq_natCast, Nat.reducePow, pow_zero, Nat.div_one]
    split_ifs <;> omega

theorem col5_longs : ∀ p ∈ col5Longs, p.2.Ok col5Spec p.1 := by
  intro p hp
  simp only [col5Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    simp only [col5Spec, spec5, nib, chiOut, callAt, ctl, callIndex, Int.ofNat_eq_natCast, Nat.reducePow, pow_zero, Nat.div_one]
    split_ifs <;> omega

theorem col6_longs : ∀ p ∈ col6Longs, p.2.Ok col6Spec p.1 := by
  intro p hp
  simp only [col6Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    simp only [col6Spec, spec6, nib, chiOut, callAt, ctl, callIndex, Int.ofNat_eq_natCast, Nat.reducePow, pow_zero, Nat.div_one]
    split_ifs <;> omega

theorem col7_longs : ∀ p ∈ col7Longs, p.2.Ok col7Spec p.1 := by
  intro p hp
  simp only [col7Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    simp only [col7Spec, spec7, nib, chiOut, callAt, ctl, callIndex, Int.ofNat_eq_natCast, Nat.reducePow, pow_zero, Nat.div_one]
    split_ifs <;> omega

theorem col8_longs : ∀ p ∈ col8Longs, p.2.Ok col8Spec p.1 := by
  intro p hp
  simp only [col8Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with ⟨k, hk, rfl⟩ | rfl
  · simp only [Shape.Ok]
    intro q hq j hj
    have a : 4096 * k + q * 16 + j < 1048576 := by omega
    have b : 4096 * k + j < 1048576 := by omega
    have h0 : nib (4096 * k + q * 16 + j) 0 = nib (4096 * k + j) 0 := by
      simp only [nib, pow_zero, Nat.div_one]; omega
    have h3 : nib (4096 * k + q * 16 + j) 3 = nib (4096 * k + j) 3 := by
      simp only [nib, Nat.reducePow]; omega
    have h4 : nib (4096 * k + q * 16 + j) 4 = nib (4096 * k + j) 4 := by
      simp only [nib, Nat.reducePow]; omega
    simp only [col8Spec, spec8, ite_eq_left a, ite_eq_left b, chiOut, Nat.reduceAdd, Nat.reduceMod, h0, h3, h4]
    simp
  · simp only [Shape.Ok]
    intro i _hi
    simp only [col8Spec, spec8, ctl, callAt, callIndex, Int.ofNat_eq_natCast]
    split_ifs <;> omega

theorem col9_longs : ∀ p ∈ col9Longs, p.2.Ok col9Spec p.1 := by
  intro p hp
  simp only [col9Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with ⟨k, hk, rfl⟩ | rfl
  · simp only [Shape.Ok]
    intro q hq j hj
    have a : 65536 * k + q * 256 + j < 1048576 := by omega
    have b : 65536 * k + j < 1048576 := by omega
    have h0 : nib (65536 * k + q * 256 + j) 0 = nib (65536 * k + j) 0 := by
      simp only [nib, pow_zero, Nat.div_one]; omega
    have h1 : nib (65536 * k + q * 256 + j) 1 = nib (65536 * k + j) 1 := by
      simp only [nib, Nat.reducePow]; omega
    have h4 : nib (65536 * k + q * 256 + j) 4 = nib (65536 * k + j) 4 := by
      simp only [nib, Nat.reducePow]; omega
    simp only [col9Spec, spec9, ite_eq_left a, ite_eq_left b, chiOut, Nat.reduceAdd, Nat.reduceMod, h0, h1, h4]
    simp
  · simp only [Shape.Ok]
    intro i _hi
    simp only [col9Spec, spec9, Int.ofNat_eq_natCast]
    split_ifs <;> omega

theorem col10_longs : ∀ p ∈ col10Longs, p.2.Ok col10Spec p.1 := by
  intro p hp
  simp only [col10Longs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl)
  all_goals
    simp only [Shape.Ok]
    intro i _hi
    simp only [col10Spec, spec10, nib, chiOut, callAt, ctl, callIndex, Int.ofNat_eq_natCast, Nat.reducePow, pow_zero, Nat.div_one]
    split_ifs <;> omega


end Airbender.Keccak.Split.Chi5.SetupProofs
