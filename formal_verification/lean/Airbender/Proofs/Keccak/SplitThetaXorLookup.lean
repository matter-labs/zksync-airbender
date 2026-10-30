import Airbender.Proofs.Keccak.SplitThetaXorValues
import Airbender.Data.Setup.Keccak.SplitControl

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup Airbender.Setup.LiteralTree
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000

/-- The arithmetic and controller views retain the same complete native source. -/
theorem xor_byte_source : thetaRhoXorSourceBytes = thetaRhoControlSourceBytes := by rfl

/-- Each actual native byte row has bounded operands, exact XOR and all physical padding fields. -/
theorem xor_byte_row_operation (index : Fin thetaRhoXor.length) :
    (thetaRhoXor.row index)[0] < 256 ∧ (thetaRhoXor.row index)[1] < 256 ∧
      (thetaRhoXor.row index)[2] < 256 ∧
      (thetaRhoXor.row index)[2] = (thetaRhoXor.row index)[0] ^^^ (thetaRhoXor.row index)[1] ∧
      (∀ column : Fin 5, (thetaRhoXor.row index)[3 + column.val] = 0) ∧
      (thetaRhoXor.row index)[8] = 4 := by
  have high : (thetaRhoXor.row index)[0] = index.val / 256 % 256 := by
    simpa only [Region.row, Vector.getElem_map] using xor_byte_high_value index.val
  have low : (thetaRhoXor.row index)[1] = index.val % 256 := by
    simpa only [Region.row, Vector.getElem_map] using xor_byte_low_value index.val
  have output : (thetaRhoXor.row index)[2] =
      (thetaRhoXor.row index)[0] ^^^ (thetaRhoXor.row index)[1] := by
    rw [high, low]
    simpa only [Region.row, Vector.getElem_map] using xor_byte_output_value index.val
  have highBound : (thetaRhoXor.row index)[0] < 256 := by rw [high]; exact Nat.mod_lt _ (by decide)
  have lowBound : (thetaRhoXor.row index)[1] < 256 := by rw [low]; exact Nat.mod_lt _ (by decide)
  refine ⟨highBound, lowBound, ?_, output, ?_, ?_⟩
  · rw [output]
    exact Nat.xor_lt_two_pow (n := 8) highBound lowBound
  · intro column
    simpa only [Region.row, Vector.getElem_map] using xor_byte_padding_value column index.val
  · simpa only [Region.row, Vector.getElem_map] using xor_byte_tag_value index.val

/-- Exact membership in the retained native field table enforces its complete byte-XOR operation. -/
theorem xor_byte_table_sound [Fact babyBearModulus.Prime] (row : Vector (ZMod babyBearModulus) 9)
    (sound : (thetaRhoXor.table "Airbender.SplitThetaRhoXor").toRaw.Soundness #[] row) :
    row[0].val < 256 ∧ row[1].val < 256 ∧ row[2].val < 256 ∧
      row[2].val = row[0].val ^^^ row[1].val ∧
      (∀ column : Fin 5, row[3 + column.val] = 0) ∧ row[8] = 4 := by
  change ∃ index : Fin thetaRhoXor.length,
    row = (thetaRhoXor.row index).map (fun value : Nat => (signedValue value : ZMod babyBearModulus)) at sound
  obtain ⟨index, rfl⟩ := sound
  have facts := xor_byte_row_operation index
  have canonical (column : Nat) (valid : column < 3) :
      (((thetaRhoXor.row index).map (fun value : Nat =>
        (signedValue value : ZMod babyBearModulus)))[column]).val = (thetaRhoXor.row index)[column] := by
    simp only [Vector.getElem_map, signedValue_cast]
    apply ZMod.val_natCast_of_lt
    have bound : (thetaRhoXor.row index)[column] < 256 := by
      have alternatives : column = 0 ∨ column = 1 ∨ column = 2 := by omega
      rcases alternatives with rfl | rfl | rfl
      · exact facts.1
      · exact facts.2.1
      · exact facts.2.2.1
    exact lt_trans bound (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [canonical 0 (by decide)]; exact facts.1
  · rw [canonical 1 (by decide)]; exact facts.2.1
  · rw [canonical 2 (by decide)]; exact facts.2.2.1
  · rw [canonical 0 (by decide), canonical 1 (by decide), canonical 2 (by decide)]
    exact facts.2.2.2.1
  · intro column
    simp only [Vector.getElem_map, signedValue_cast, facts.2.2.2.2.1 column, Nat.cast_zero]
  · simp only [Vector.getElem_map, signedValue_cast, facts.2.2.2.2.2, Nat.cast_ofNat]

end Airbender.Keccak.Split.Native.Fixed.Proofs
