module
public import Proven.KeccakSplit.Setup.ColumnParity.Shapes

@[expose] public section

/- Agreement of every listed long block with its row formula, by formula: grid blocks by
   their digits (`digits_eq`), affine runs by `omega`. -/

namespace Airbender.Keccak.Split.ColumnParity.SetupProofs

open Airbender.Import.Setup Airbender.Import.Setup.Proofs Airbender.Keccak.Split.SetupProofs

set_option warningAsError true
-- generated (gen/setup/genk.py): every block gets the same simp set, which a block need not use in full
set_option linter.unusedSimpArgs false

theorem iotaTable_eq : ∀ b < 256, iotaTable.getD b 0 = rcByte b := by decide +kernel

theorem col0_longs : ∀ p ∈ col0Longs, p.2.Ok col0Spec p.1 := by
  intro p hp
  simp only [col0Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col0Spec, spec0, nib, callAt, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col1_longs : ∀ p ∈ col1Longs, p.2.Ok col1Spec p.1 := by
  intro p hp
  simp only [col1Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col1Spec, spec1, nib, callAt, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col2_longs : ∀ p ∈ col2Longs, p.2.Ok col2Spec p.1 := by
  intro p hp
  simp only [col2Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col2Spec, spec2, nib, callAt, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    try rw [iotaTable_eq _ (by omega)]
    split_ifs <;> digits_eq

theorem col3_longs : ∀ p ∈ col3Longs, p.2.Ok col3Spec p.1 := by
  intro p hp
  simp only [col3Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col3Spec, spec3, nib, callAt, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col4_longs : ∀ p ∈ col4Longs, p.2.Ok col4Spec p.1 := by
  intro p hp
  simp only [col4Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col4Spec, spec4, nib, callAt, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col5_longs : ∀ p ∈ col5Longs, p.2.Ok col5Spec p.1 := by
  intro p hp
  simp only [col5Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col5Spec, spec5, nib, callAt, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col6_longs : ∀ p ∈ col6Longs, p.2.Ok col6Spec p.1 := by
  intro p hp
  simp only [col6Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col6Spec, spec6, nib, callAt, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

theorem col7_longs : ∀ p ∈ col7Longs, p.2.Ok col7Spec p.1 := by
  intro p hp
  simp only [col7Longs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  all_goals
    intro i hi
    simp only [GridFn.eval, GridFn.nibble, col7Spec, spec7, nib, callAt, callIndex, Nat.reducePow, pow_zero, Nat.div_one, Nat.zero_add,
      Int.ofNat_eq_natCast, Nat.cast_inj]
    split_ifs <;> digits_eq

end Airbender.Keccak.Split.ColumnParity.SetupProofs
