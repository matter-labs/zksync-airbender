import Airbender.Proofs.Keccak.SplitChiOutputs

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000

private theorem chi5_tag_column : chi5Generic.columns[10] =
    ⟨#[.affine 1048576 65 0, .affine 121 66 0, .affine 3145607 0 0]⟩ := by rfl

/-- The native chi tag selects the arithmetic region of the complete generic table. -/
theorem chi5_arithmetic_field_tag_region (index : Fin chi5Generic.length)
    (tag : ((chi5Generic.row index).map (fun value : Int => (value : ZMod babyBearModulus)))[10] = 65) :
    index.val < 1048576 := by
  simp only [TableData.row, Vector.getElem_map] at tag
  change (signedValue ((chi5Generic.columns[10].get? (0 + index.val)).getD 0) : ZMod babyBearModulus) = 65 at tag
  rw [Nat.zero_add, chi5_tag_column] at tag
  simp only [Column.get?, getFromBlocks, Block.get?, Block.length] at tag
  split_ifs at tag
  all_goals try simp only [zero_mul, add_zero] at tag
  all_goals first
    | omega
    | (have values := congrArg ZMod.val tag
       simp only [Option.getD_some, Option.getD_none, Int.toNat_natCast, signedValue_cast] at values
       first
       | change 66 = 65 at values; omega
       | change 0 = 65 at values; omega)

private theorem nibble_chi_bound : ∀ a b c : Fin 16,
    a.val ^^^ ((15 ^^^ b.val) &&& c.val) < 16 := by decide +kernel

/-- Native tagged chi lookup derives input bounds, output bounds and exact chi. -/
theorem chi5_generic_lookup_sound [Fact babyBearModulus.Prime]
    (row : Vector (ZMod babyBearModulus) 11)
    (sound : (chi5Generic.table "Airbender.SplitChi5Generic").toRaw.Soundness #[] row)
    (tag : row[10] = 65) :
    (∀ column : Fin 5, row[column.val].val < 16) ∧
    (∀ column : Fin 5, row[5 + column.val].val < 16 ∧
      row[5 + column.val].val = row[column.val].val ^^^
        ((15 ^^^ row[(column.val + 1) % 5].val) &&& row[(column.val + 2) % 5].val)) := by
  change ∃ index : Fin chi5Generic.length,
    row = (chi5Generic.row index).map (fun value : Int => (value : ZMod babyBearModulus)) at sound
  obtain ⟨index, rfl⟩ := sound
  let rowPrefix : Fin 1048576 := ⟨index.val, chi5_arithmetic_field_tag_region index tag⟩
  have field (column : Nat) (included : column < 11) (value : Nat)
      (actual : chi5Generic.columns[column].get? index.val = some value) (small : value < 16) :
      (((chi5Generic.row index).map (fun value : Int => (value : ZMod babyBearModulus)))[column]).val = value := by
    simp only [TableData.row, Vector.getElem_map]
    change (signedValue ((chi5Generic.columns[column].get? (0 + index.val)).getD 0) : ZMod babyBearModulus).val = value
    rw [Nat.zero_add, actual, Option.getD_some, signedValue_cast,
      ZMod.val_natCast_of_lt (lt_trans small (by decide : 16 < babyBearModulus))]
  have input (column : Fin 5) :
      (((chi5Generic.row index).map (fun value : Int => (value : ZMod babyBearModulus)))[column.val]).val =
        index.val / 16 ^ column.val % 16 := by
    exact field column.val (by omega) _ (chi5_input_get column rowPrefix) (Nat.mod_lt _ (by decide))
  refine ⟨?_, ?_⟩
  · intro column
    rw [input column]
    exact Nat.mod_lt _ (by decide)
  · intro column
    let a : Fin 16 := ⟨index.val / 16 ^ column.val % 16, Nat.mod_lt _ (by decide)⟩
    let b : Fin 16 := ⟨index.val / 16 ^ ((column.val + 1) % 5) % 16, Nat.mod_lt _ (by decide)⟩
    let c : Fin 16 := ⟨index.val / 16 ^ ((column.val + 2) % 5) % 16, Nat.mod_lt _ (by decide)⟩
    have bound := nibble_chi_bound a b c
    have selected := chi5_output_get column rowPrefix
    have operation := chi5_output_value column rowPrefix
    rw [selected, Option.getD_some] at operation
    have actual := selected.trans (congrArg some operation)
    have value := field (5 + column.val) (by omega) _ actual bound
    refine ⟨?_, ?_⟩
    · rw [value]
      exact bound
    · rw [value, input column,
        input ⟨(column.val + 1) % 5, Nat.mod_lt _ (by decide)⟩,
        input ⟨(column.val + 2) % 5, Nat.mod_lt _ (by decide)⟩]

end Airbender.Keccak.Split.Native.Fixed.Proofs
