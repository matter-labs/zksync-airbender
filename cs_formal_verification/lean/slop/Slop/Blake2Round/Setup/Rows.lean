import Slop.Blake2Round.Setup.Col0Walk
import Slop.Blake2Round.Setup.Col1Walk
import Slop.Blake2Round.Setup.Col2Part0
import Slop.Blake2Round.Setup.Col2Part1
import Slop.Blake2Round.Setup.Col2Part2
import Slop.Blake2Round.Setup.Col2Part3
import Slop.Blake2Round.Setup.Col2Part4
import Slop.Blake2Round.Setup.Col3Part0
import Slop.Blake2Round.Setup.Col3Part1
import Slop.Blake2Round.Setup.Col3Part2
import Slop.Blake2Round.Setup.Col4Walk
import Slop.Blake2Round.Setup.Col5Walk
import Mathlib.Tactic.IntervalCases
import Human.Circuits.Blake2Round.Tables.Setup

/- Row meaning of the imported setup: every column decodes to its row formula on
   all 2^20 exported rows. Short blocks come from the kernel walks; long blocks
   are affine or periodic shapes checked here algebraically, never expanded. -/

namespace Airbender.Blake2Round.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option maxHeartbeats 1000000


theorem col0_longs : ∀ p ∈ col0Longs, p.2.Ok col0Spec p.1 := by
  intro p hp
  simp only [col0Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Shape.Ok]
    intro i _
    try intros
    simp only [spec0, Int.ofNat_eq_natCast]
    split_ifs <;> omega

theorem col1_longs : ∀ p ∈ col1Longs, p.2.Ok col1Spec p.1 := by
  intro p hp
  simp only [col1Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Shape.Ok]
    intro i _
    try intros
    simp only [spec1, Int.ofNat_eq_natCast]
    split_ifs <;> omega

theorem col2_longs : ∀ p ∈ col2Longs, p.2.Ok col2Spec p.1 := by
  intro p hp
  simp only [col2Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Shape.Ok]
    intro i _
    try intros
    simp only [spec2, Int.ofNat_eq_natCast]
    split_ifs <;> omega

theorem col3_longs : ∀ p ∈ col3Longs, p.2.Ok col3Spec p.1 := by
  intro p hp
  simp only [col3Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  all_goals
    simp only [Shape.Ok]
    intro i _
    try intros
    simp only [spec3, Int.ofNat_eq_natCast]
    split_ifs <;> first
      | omega
      | ((obtain rfl : i = 344064 := by omega); decide)

theorem col4_longs : ∀ p ∈ col4Longs, p.2.Ok col4Spec p.1 := by
  intro p hp
  simp only [col4Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    simp only [Shape.Ok]
    intro i _
    try intros
    simp only [spec4, Int.ofNat_eq_natCast]
    split_ifs <;> first
      | omega
      | ((obtain rfl : i = 589824 := by omega); decide)

theorem col5_longs : ∀ p ∈ col5Longs, p.2.Ok col5Spec p.1 := by
  intro p hp
  simp only [col5Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Shape.Ok]
    intro i _
    try intros
    simp only [spec5, Int.ofNat_eq_natCast]
    split_ifs <;> omega

theorem col0_total : total blake2RoundSetup_col0 = 1048576 := by decide +kernel

theorem col0_rows : ∀ n < 1048576, decode blake2RoundSetup_col0 n = col0Spec n := by
  rw [← col0_total]
  apply decode_eq
  intro p hp
  have le := placed_le p hp
  rw [col0_total] at le
  exact walk_sound col0_longs col0_walk p hp (by omega) (by omega)

theorem col1_total : total blake2RoundSetup_col1 = 1048576 := by decide +kernel

theorem col1_rows : ∀ n < 1048576, decode blake2RoundSetup_col1 n = col1Spec n := by
  rw [← col1_total]
  apply decode_eq
  intro p hp
  have le := placed_le p hp
  rw [col1_total] at le
  exact walk_sound col1_longs col1_walk p hp (by omega) (by omega)

theorem col2_total : total blake2RoundSetup_col2 = 1048576 := by decide +kernel

theorem col2_rows : ∀ n < 1048576, decode blake2RoundSetup_col2 n = col2Spec n := by
  rw [← col2_total]
  apply decode_eq
  intro p hp
  have le := placed_le p hp
  rw [col2_total] at le
  by_cases h0 : p.1 < 65536
  · exact walk_sound col2_longs col2_part0 p hp (by omega) h0
  by_cases h1 : p.1 < 81920
  · exact walk_sound col2_longs col2_part1 p hp (by omega) h1
  by_cases h2 : p.1 < 212992
  · exact walk_sound col2_longs col2_part2 p hp (by omega) h2
  by_cases h3 : p.1 < 344064
  · exact walk_sound col2_longs col2_part3 p hp (by omega) h3
  exact walk_sound col2_longs col2_part4 p hp (by omega) (by omega)

theorem col3_total : total blake2RoundSetup_col3 = 1048576 := by decide +kernel

theorem col3_rows : ∀ n < 1048576, decode blake2RoundSetup_col3 n = col3Spec n := by
  rw [← col3_total]
  apply decode_eq
  intro p hp
  have le := placed_le p hp
  rw [col3_total] at le
  by_cases h0 : p.1 < 442368
  · exact walk_sound col3_longs col3_part0 p hp (by omega) h0
  by_cases h1 : p.1 < 540672
  · exact walk_sound col3_longs col3_part1 p hp (by omega) h1
  exact walk_sound col3_longs col3_part2 p hp (by omega) (by omega)

theorem col4_total : total blake2RoundSetup_col4 = 1048576 := by decide +kernel

theorem col4_rows : ∀ n < 1048576, decode blake2RoundSetup_col4 n = col4Spec n := by
  rw [← col4_total]
  apply decode_eq
  intro p hp
  have le := placed_le p hp
  rw [col4_total] at le
  exact walk_sound col4_longs col4_walk p hp (by omega) (by omega)

theorem col5_total : total blake2RoundSetup_col5 = 1048576 := by decide +kernel

theorem col5_rows : ∀ n < 1048576, decode blake2RoundSetup_col5 n = col5Spec n := by
  rw [← col5_total]
  apply decode_eq
  intro p hp
  have le := placed_le p hp
  rw [col5_total] at le
  exact walk_sound col5_longs col5_walk p hp (by omega) (by omega)

/-- The row formulas, one per column. -/
def formulaRow (n : Nat) : Vector Nat 6 := #v[spec0 n, spec1 n, spec2 n, spec3 n, spec4 n, spec5 n]

theorem traceLen_eq : blake2RoundSetup.traceLen = 1048576 := rfl

/-- Every exported row is the formula row. -/
theorem setupRow_eq (n : Nat) (hn : n < 1048576) :
    setupRow n = (formulaRow n).map Int.ofNat := by
  ext c hc
  simp only [setupRow, Vector.getElem_ofFn, Vector.getElem_map, formulaRow]
  interval_cases c
  · exact col0_rows n hn
  · exact col1_rows n hn
  · exact col2_rows n hn
  · exact col3_rows n hn
  · exact col4_rows n hn
  · exact col5_rows n hn

end Airbender.Blake2Round.SetupProofs
