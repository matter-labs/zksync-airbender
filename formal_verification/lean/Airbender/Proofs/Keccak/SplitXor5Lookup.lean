import Airbender.Proofs.Keccak.SplitXor5Outputs
import Airbender.Data.Setup.Keccak.ColumnParityControl

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup Airbender.Setup.LiteralTree
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000

/-- The literal arithmetic view retains the same complete native source as the controller. -/
theorem xor5_source : columnParityXor5SourceBytes = columnParityControlSourceBytes := by rfl

/-- Every actual literal row has bounded nibble inputs and its exact XOR output. -/
theorem xor5_row_operation (index : Fin columnParityXor5.length) :
    (∀ column : Fin 5, (columnParityXor5.row index)[column.val] < 16) ∧
      (columnParityXor5.row index)[5] < 16 ∧
      (columnParityXor5.row index)[5] =
        (columnParityXor5.row index)[0] ^^^ (columnParityXor5.row index)[1] ^^^
          (columnParityXor5.row index)[2] ^^^ (columnParityXor5.row index)[3] ^^^ (columnParityXor5.row index)[4] ∧
      (columnParityXor5.row index)[6] = 0 ∧ (columnParityXor5.row index)[7] = 64 := by
  have input (column : Fin 5) : (columnParityXor5.row index)[column.val] =
      index.val / 16 ^ column.val % 16 := by
    simpa only [Region.row, Vector.getElem_map] using xor5_key_values column index.val
  have inputNat (column : Nat) (valid : column < 5) : (columnParityXor5.row index)[column] =
      index.val / 16 ^ column % 16 := input ⟨column, valid⟩
  have bound (column : Fin 5) : (columnParityXor5.row index)[column.val] < 16 := by
    rw [input column]
    exact Nat.mod_lt _ (by decide)
  have output : (columnParityXor5.row index)[5] =
      (columnParityXor5.row index)[0] ^^^ (columnParityXor5.row index)[1] ^^^
        (columnParityXor5.row index)[2] ^^^ (columnParityXor5.row index)[3] ^^^ (columnParityXor5.row index)[4] := by
    rw [inputNat 0 (by decide), inputNat 1 (by decide), inputNat 2 (by decide),
      inputNat 3 (by decide), inputNat 4 (by decide)]
    simpa only [Region.row, Vector.getElem_map, Nat.reducePow, Nat.div_one] using xor5_output_value index.val
  have small01 := Nat.xor_lt_two_pow (n := 4) (bound 0) (bound 1)
  have small012 := Nat.xor_lt_two_pow (n := 4) small01 (bound 2)
  have small0123 := Nat.xor_lt_two_pow (n := 4) small012 (bound 3)
  have smallOutput : (columnParityXor5.row index)[5] < 16 := by
    rw [output]
    exact Nat.xor_lt_two_pow (n := 4) small0123 (bound 4)
  have fixed : (columnParityXor5.row index)[6] = 0 ∧ (columnParityXor5.row index)[7] = 64 := by
    simpa only [Region.row, Vector.getElem_map] using xor5_fixed_values index.val
  exact ⟨bound, smallOutput, output, fixed⟩

/-- Native field membership in the complete XOR table proves the actual five-input operation. -/
theorem xor5_table_sound [Fact babyBearModulus.Prime] (row : Vector (ZMod babyBearModulus) 8)
    (sound : (columnParityXor5.table "Airbender.SplitColumnParityXor5").toRaw.Soundness #[] row) :
    (∀ column : Fin 5, row[column.val].val < 16) ∧ row[5].val < 16 ∧
      row[5].val = row[0].val ^^^ row[1].val ^^^ row[2].val ^^^ row[3].val ^^^ row[4].val ∧
      row[6] = 0 ∧ row[7] = 64 := by
  change ∃ index : Fin columnParityXor5.length,
    row = (columnParityXor5.row index).map (fun value : Nat => (signedValue value : ZMod babyBearModulus)) at sound
  obtain ⟨index, rfl⟩ := sound
  have facts := xor5_row_operation index
  have canonical (column : Fin 6) :
      (((columnParityXor5.row index).map (fun value : Nat =>
        (signedValue value : ZMod babyBearModulus)))[column.val]).val = (columnParityXor5.row index)[column.val] := by
    simp only [Vector.getElem_map, signedValue_cast]
    apply ZMod.val_natCast_of_lt
    have bound : (columnParityXor5.row index)[column.val] < 16 := by
      by_cases input : column.val < 5
      · exact facts.1 ⟨column.val, input⟩
      · have same : column.val = 5 := by have := column.isLt; omega
        simpa only [same] using facts.2.1
    exact lt_trans bound (by decide)
  have canonicalNat (column : Nat) (valid : column < 6) :
      (((columnParityXor5.row index).map (fun value : Nat =>
        (signedValue value : ZMod babyBearModulus)))[column]).val = (columnParityXor5.row index)[column] :=
    canonical ⟨column, valid⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro column
    rw [canonical ⟨column.val, by have := column.isLt; omega⟩]
    exact facts.1 column
  · rw [canonicalNat 5 (by decide)]
    exact facts.2.1
  · rw [canonicalNat 0 (by decide), canonicalNat 1 (by decide), canonicalNat 2 (by decide),
      canonicalNat 3 (by decide), canonicalNat 4 (by decide), canonicalNat 5 (by decide)]
    exact facts.2.2.1
  · simp only [Vector.getElem_map, signedValue_cast, facts.2.2.2.1, Nat.cast_zero]
  · simp only [Vector.getElem_map, signedValue_cast, facts.2.2.2.2, Nat.cast_ofNat]

end Airbender.Keccak.Split.Native.Fixed.Proofs
