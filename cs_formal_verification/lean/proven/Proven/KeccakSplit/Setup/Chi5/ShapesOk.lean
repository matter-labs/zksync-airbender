module
public import Proven.KeccakSplit.Setup.Chi5.Shapes

@[expose] public section

/- Agreement of every listed long block with its row formula, by formula: grid blocks by
   their digits (`digits_eq`), affine runs by `omega`. -/

namespace Airbender.Keccak.Split.Chi5.SetupProofs

open Airbender.Import.Setup Airbender.Import.Setup.Proofs Airbender.Keccak.Split.SetupProofs

set_option warningAsError true
-- generated (gen/setup/genk.py): every block gets the same simp set, which a block need not use in full
set_option linter.unusedSimpArgs false

theorem col0_longs : ∀ p ∈ col0Longs, p.2.Ok col0Spec p.1 := by
  intro p hp
  simp only [col0Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col0Spec, spec0, nib, chiOut, callAt, ctl, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col1_longs : ∀ p ∈ col1Longs, p.2.Ok col1Spec p.1 := by
  intro p hp
  simp only [col1Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col1Spec, spec1, nib, chiOut, callAt, ctl, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col2_longs : ∀ p ∈ col2Longs, p.2.Ok col2Spec p.1 := by
  intro p hp
  simp only [col2Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col2Spec, spec2, nib, chiOut, callAt, ctl, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col3_longs : ∀ p ∈ col3Longs, p.2.Ok col3Spec p.1 := by
  intro p hp
  simp only [col3Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col3Spec, spec3, nib, chiOut, callAt, ctl, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col4_longs : ∀ p ∈ col4Longs, p.2.Ok col4Spec p.1 := by
  intro p hp
  simp only [col4Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col4Spec, spec4, nib, chiOut, callAt, ctl, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col5_longs : ∀ p ∈ col5Longs, p.2.Ok col5Spec p.1 := by
  intro p hp
  simp only [col5Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col5Spec, spec5, nib, chiOut, callAt, ctl, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col6_longs : ∀ p ∈ col6Longs, p.2.Ok col6Spec p.1 := by
  intro p hp
  simp only [col6Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col6Spec, spec6, nib, chiOut, callAt, ctl, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col7_longs : ∀ p ∈ col7Longs, p.2.Ok col7Spec p.1 := by
  intro p hp
  simp only [col7Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col7Spec, spec7, nib, chiOut, callAt, ctl, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col8_longs : ∀ p ∈ col8Longs, p.2.Ok col8Spec p.1 := by
  intro p hp
  simp only [col8Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col8Spec, spec8, nib, chiOut, callAt, ctl, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col9_longs : ∀ p ∈ col9Longs, p.2.Ok col9Spec p.1 := by
  intro p hp
  simp only [col9Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col9Spec, spec9, nib, chiOut, callAt, ctl, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col10_longs : ∀ p ∈ col10Longs, p.2.Ok col10Spec p.1 := by
  intro p hp
  simp only [col10Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col10Spec, spec10, nib, chiOut, callAt, ctl, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

end Airbender.Keccak.Split.Chi5.SetupProofs
