import Airbender.Proofs.Keccak.SplitThetaFragmentValues
import Airbender.Proofs.Keccak.SplitThetaSplitKeys
import Airbender.Proofs.Keccak.SplitThetaXorLookup

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup Airbender.Setup.LiteralTree
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false

/-- The split arithmetic and controller views retain the same complete native source. -/
theorem theta_split_source : thetaRhoXorSplitSourceBytes = thetaRhoControlSourceBytes := by rfl

/-- Every actual split row has bounded keys, exact fragments and all physical padding fields. -/
theorem theta_split_row_operation (index : Fin thetaRhoXorSplit.length) :
    (thetaRhoXorSplit.row index)[0] < 256 ∧ (thetaRhoXorSplit.row index)[1] < 256 ∧
      (thetaRhoXorSplit.row index)[2] < 8 ∧
      (thetaRhoXorSplit.row index)[3] < 256 ∧ (thetaRhoXorSplit.row index)[4] < 256 ∧
      (thetaRhoXorSplit.row index)[3] =
        ((thetaRhoXorSplit.row index)[0] ^^^ (thetaRhoXorSplit.row index)[1]) *
          2 ^ (thetaRhoXorSplit.row index)[2] % 256 ∧
      (thetaRhoXorSplit.row index)[4] =
        ((thetaRhoXorSplit.row index)[0] ^^^ (thetaRhoXorSplit.row index)[1]) /
          2 ^ (8 - (thetaRhoXorSplit.row index)[2]) ∧
      (∀ column : Fin 3, (thetaRhoXorSplit.row index)[5 + column.val] = 0) ∧
      (thetaRhoXorSplit.row index)[8] = 58 := by
  have first : (thetaRhoXorSplit.row index)[0] = index.val % 256 := by
    simpa only [Region.row, Vector.getElem_map] using theta_split_first_value index
  have second : (thetaRhoXorSplit.row index)[1] = index.val / 256 % 256 := by
    simpa only [Region.row, Vector.getElem_map] using theta_split_second_value index
  have shift : (thetaRhoXorSplit.row index)[2] = index.val / 65536 := by
    simpa only [Region.row, Vector.getElem_map] using theta_split_shift_value index
  have low : (thetaRhoXorSplit.row index)[3] =
      ((thetaRhoXorSplit.row index)[0] ^^^ (thetaRhoXorSplit.row index)[1]) *
        2 ^ (thetaRhoXorSplit.row index)[2] % 256 := by
    rw [first, second, shift, Nat.xor_comm (index.val % 256)]
    simpa only [Region.row, Vector.getElem_map] using theta_fragment_low_value index
  have high : (thetaRhoXorSplit.row index)[4] =
      ((thetaRhoXorSplit.row index)[0] ^^^ (thetaRhoXorSplit.row index)[1]) /
        2 ^ (8 - (thetaRhoXorSplit.row index)[2]) := by
    rw [first, second, shift, Nat.xor_comm (index.val % 256)]
    simpa only [Region.row, Vector.getElem_map] using theta_fragment_high_value index
  have firstBound : (thetaRhoXorSplit.row index)[0] < 256 := by
    rw [first]; exact Nat.mod_lt _ (by decide)
  have secondBound : (thetaRhoXorSplit.row index)[1] < 256 := by
    rw [second]; exact Nat.mod_lt _ (by decide)
  have xorBound := Nat.xor_lt_two_pow (n := 8) firstBound secondBound
  refine ⟨firstBound, secondBound, ?_, ?_, ?_, low, high, ?_, ?_⟩
  · rw [shift]
    have bound : index.val < 524288 := index.isLt
    omega
  · rw [low]; exact Nat.mod_lt _ (by decide)
  · rw [high]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) xorBound
  · intro column
    simpa only [Region.row, Vector.getElem_map] using theta_split_padding_value column index.val
  · simpa only [Region.row, Vector.getElem_map] using theta_split_tag_value index

/-- Exact membership in the retained native field table enforces both complete shifted XOR fragments. -/
theorem theta_split_table_sound [Fact babyBearModulus.Prime] (row : Vector (ZMod babyBearModulus) 9)
    (sound : (thetaRhoXorSplit.table "Airbender.SplitThetaRhoXorSplit").toRaw.Soundness #[] row) :
    row[0].val < 256 ∧ row[1].val < 256 ∧ row[2].val < 8 ∧
      row[3].val < 256 ∧ row[4].val < 256 ∧
      row[3].val = (row[0].val ^^^ row[1].val) * 2 ^ row[2].val % 256 ∧
      row[4].val = (row[0].val ^^^ row[1].val) / 2 ^ (8 - row[2].val) ∧
      (∀ column : Fin 3, row[5 + column.val] = 0) ∧ row[8] = 58 := by
  change ∃ index : Fin thetaRhoXorSplit.length,
    row = (thetaRhoXorSplit.row index).map (fun value : Nat => (signedValue value : ZMod babyBearModulus)) at sound
  obtain ⟨index, rfl⟩ := sound
  have facts := theta_split_row_operation index
  have canonical (column : Nat) (valid : column < 5) :
      (((thetaRhoXorSplit.row index).map (fun value : Nat =>
        (signedValue value : ZMod babyBearModulus)))[column]).val =
          (thetaRhoXorSplit.row index)[column] := by
    simp only [Vector.getElem_map, signedValue_cast]
    apply ZMod.val_natCast_of_lt
    have bound : (thetaRhoXorSplit.row index)[column] < 256 := by
      have alternatives : column = 0 ∨ column = 1 ∨ column = 2 ∨ column = 3 ∨ column = 4 := by omega
      rcases alternatives with rfl | rfl | rfl | rfl | rfl
      · exact facts.1
      · exact facts.2.1
      · exact lt_trans facts.2.2.1 (by decide)
      · exact facts.2.2.2.1
      · exact facts.2.2.2.2.1
    exact lt_trans bound (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [canonical 0 (by decide)]; exact facts.1
  · rw [canonical 1 (by decide)]; exact facts.2.1
  · rw [canonical 2 (by decide)]; exact facts.2.2.1
  · rw [canonical 3 (by decide)]; exact facts.2.2.2.1
  · rw [canonical 4 (by decide)]; exact facts.2.2.2.2.1
  · rw [canonical 0 (by decide), canonical 1 (by decide), canonical 2 (by decide), canonical 3 (by decide)]
    exact facts.2.2.2.2.2.1
  · rw [canonical 0 (by decide), canonical 1 (by decide), canonical 2 (by decide), canonical 4 (by decide)]
    exact facts.2.2.2.2.2.2.1
  · intro column
    simp only [Vector.getElem_map, signedValue_cast, facts.2.2.2.2.2.2.2.1 column, Nat.cast_zero]
  · simp only [Vector.getElem_map, signedValue_cast, facts.2.2.2.2.2.2.2.2, Nat.cast_ofNat]

end Airbender.Keccak.Split.Native.Fixed.Proofs
