import Slop.Blake2Round.Setup.Spec
import Mathlib.Tactic.IntervalCases
import Human.Circuits.Blake2Round.Tables.Setup

/- Row meaning of the imported setup: every column decodes to its row formula on all 2^20
   exported rows. Each column is a few blocks (the import's grid blocks for the six table
   regions, affine runs for the rest), matched by shape (`Spec.col*Longs`) and proved here
   by formula, never expanded. -/

namespace Airbender.Blake2Round.SetupProofs
open Airbender.Import.Setup Airbender.Import.Setup.Proofs

set_option warningAsError true

theorem col0_longs : ∀ p ∈ col0Longs, p.2.Ok col0Spec p.1 := by
  intro p hp
  simp only [col0Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, col0Spec, spec0, Nat.zero_add, Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col0_rows : ∀ n < 1048576, decode blake2RoundSetup_col0 n = col0Spec n :=
  rows_of_scan _ col0_longs (by decide +kernel) (by decide +kernel)

theorem col1_longs : ∀ p ∈ col1Longs, p.2.Ok col1Spec p.1 := by
  intro p hp
  simp only [col1Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, col1Spec, spec1, Nat.zero_add, Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col1_rows : ∀ n < 1048576, decode blake2RoundSetup_col1 n = col1Spec n :=
  rows_of_scan _ col1_longs (by decide +kernel) (by decide +kernel)

theorem col2_longs : ∀ p ∈ col2Longs, p.2.Ok col2Spec p.1 := by
  intro p hp
  simp only [col2Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, col2Spec, spec2, Nat.zero_add, Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col2_rows : ∀ n < 1048576, decode blake2RoundSetup_col2 n = col2Spec n :=
  rows_of_scan _ col2_longs (by decide +kernel) (by decide +kernel)

theorem col3_longs : ∀ p ∈ col3Longs, p.2.Ok col3Spec p.1 := by
  intro p hp
  simp only [col3Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, col3Spec, spec3, Nat.zero_add, Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col3_rows : ∀ n < 1048576, decode blake2RoundSetup_col3 n = col3Spec n :=
  rows_of_scan _ col3_longs (by decide +kernel) (by decide +kernel)

theorem col4_longs : ∀ p ∈ col4Longs, p.2.Ok col4Spec p.1 := by
  intro p hp
  simp only [col4Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, col4Spec, spec4, Nat.zero_add, Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col4_rows : ∀ n < 1048576, decode blake2RoundSetup_col4 n = col4Spec n :=
  rows_of_scan _ col4_longs (by decide +kernel) (by decide +kernel)

theorem col5_longs : ∀ p ∈ col5Longs, p.2.Ok col5Spec p.1 := by
  intro p hp
  simp only [col5Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro i hi
    simp only [col5Spec, spec5, Nat.zero_add, Int.ofNat_eq_natCast]
    split_ifs <;> digits_eq

theorem col5_rows : ∀ n < 1048576, decode blake2RoundSetup_col5 n = col5Spec n :=
  rows_of_scan _ col5_longs (by decide +kernel) (by decide +kernel)

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
