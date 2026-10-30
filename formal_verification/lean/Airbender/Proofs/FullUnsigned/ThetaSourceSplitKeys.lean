import Airbender.Proofs.FullUnsigned.SourceBlockWindows
import Airbender.Proofs.FullUnsigned.SourceFirstBlocks
import Airbender.Proofs.FullUnsigned.Source.Theta
import Airbender.Proofs.Keccak.SplitThetaSplitKeys
import Airbender.Proofs.Tables.PeriodicColumns

namespace Airbender.Setup.SourceCaptureThetaProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
-- Each key window has at most eight blocks. Each periodic template has 256 values.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private noncomputable def sourceColumn (column : Fin 9) : Column :=
  (SourceCaptureTheta.columns[column.val]?).getD ⟨#[]⟩

private noncomputable def keyWindow (column : Fin 3) : List Block :=
  ((sourceColumn ⟨column.val, by omega⟩).blocks.toList.drop (if column.val = 2 then 898 else 1)).take
    (if column.val = 0 then 1 else 8)

private theorem key_offsets (column : Fin 3) :
    (((sourceColumn ⟨column.val, by omega⟩).blocks.toList.take (if column.val = 2 then 898 else 1)).map Block.length).sum = 65536 := by
  fin_cases column <;> setup_source_rfl

private theorem low_shape : keyWindow ⟨0, by decide +kernel⟩ =
    [.periodic 2048 0 (Array.range 256)] := by setup_source_rfl

private theorem high_shape : keyWindow ⟨1, by decide +kernel⟩ =
    List.replicate 8 (.periodic 256 1 (Array.replicate 256 0)) := by setup_source_rfl

private theorem shift_shape : keyWindow ⟨2, by decide +kernel⟩ =
    (List.range 8).map (fun shift => Block.affine 65536 shift 0) := by setup_source_rfl

private theorem key_lengths (column : Fin 3) :
    ((keyWindow column).map Block.length).sum = 524288 := by
  fin_cases column <;> setup_source_rfl

private theorem source_key_window (column : Fin 3) (index : Fin 524288) :
    ((SourceCaptureTheta.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val) =
      getFromBlocks (keyWindow column) index.val := by
  exact getFromBlocks_window _ _ _ _ _ (key_offsets column) (by
    change index.val < ((keyWindow column).map Block.length).sum
    rw [key_lengths]
    exact index.isLt)

/-- The split source first key is the low byte of its local row coordinate. -/
theorem source_split_first_get (index : Fin 524288) :
    ((SourceCaptureTheta.columns[0]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val) =
      some (index.val % 256) := by
  rw [source_key_window (⟨0, by decide +kernel⟩ : Fin 3) index, low_shape]
  have bound : index.val < (Block.periodic 2048 0 (Array.range 256)).length := by
    simpa only [Block.length, Array.size_range] using index.isLt
  rw [getFromBlocks, if_pos bound]
  have value := periodic_get (Array.range 256) 2048 0 index.val (by simp)
    (by simpa only [Array.size_range] using index.isLt)
  simpa only [Array.size_range, Array.getElem_range, Nat.zero_mul, Nat.add_zero, Int.natCast_zero] using value

/-- The split source second key is the next byte of its local row coordinate. -/
theorem source_split_second_get (index : Fin 524288) :
    ((SourceCaptureTheta.columns[1]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val) =
      some (index.val / 256 % 256) := by
  rw [source_key_window (⟨1, by decide +kernel⟩ : Fin 3) index, high_shape]
  have blockLengths : ∀ block ∈ List.replicate 8 (Block.periodic 256 1 (Array.replicate 256 0)),
      block.length = 65536 := by
    intro block member
    have same := (List.mem_replicate.mp member).2
    rw [same]
    rfl
  rw [uniform65536_get _ blockLengths]
  have high : index.val / 65536 < 8 := by omega
  rw [List.getElem?_replicate_of_lt high, Option.bind_some]
  have value := periodic_get (Array.replicate 256 0) 256 1 (index.val % 65536) (by simp)
    (by simpa only [Array.size_replicate] using Nat.mod_lt index.val (by decide : 0 < 65536))
  have quotient : index.val % 65536 / 256 = index.val / 256 % 256 := by omega
  simpa only [Array.size_replicate, Array.getElem_replicate, Nat.zero_add, Nat.one_mul,
    Int.natCast_one, quotient] using value

/-- The third source key is the complete native shift from zero through seven. -/
theorem source_split_shift_get (index : Fin 524288) :
    ((SourceCaptureTheta.columns[2]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val) =
      some (index.val / 65536) := by
  rw [source_key_window (⟨2, by decide +kernel⟩ : Fin 3) index, shift_shape]
  have blockLengths : ∀ block ∈ (List.range 8).map (fun shift => Block.affine 65536 shift 0),
      block.length = 65536 := by
    intro block member
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    rfl
  rw [uniform65536_get _ blockLengths]
  have high : index.val / 65536 < 8 := by omega
  simp only [List.getElem?_map, List.getElem?_range, high, Option.map_some, Option.bind_some]
  exact constant_affine_get _ _ _ (Nat.mod_lt _ (by decide : 0 < 65536))

private def paddingBlock (column : Fin 3) : Block := .affine (589827 + column.val) 0 0

private theorem padding_head (column : Fin 3) :
    ((sourceColumn ⟨5 + column.val, by omega⟩).blocks.toList).head? = some (paddingBlock column) := by
  fin_cases column <;> setup_source_rfl

/-- All three unused source fields stay zero on the full split arithmetic region. -/
theorem source_split_padding_get (column : Fin 3) (index : Fin 524288) :
    ((SourceCaptureTheta.columns[5 + column.val]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val) = some 0 := by
  have bound : 65536 + index.val < (paddingBlock column).length := by
    change 65536 + index.val < 589827 + column.val
    have upper := index.isLt
    omega
  exact (getFromBlocks_first _ _ _ (padding_head column) bound).trans
    (constant_affine_get _ _ _ bound)

private theorem tag_offset :
    (((sourceColumn ⟨8, by decide +kernel⟩).blocks.toList.take 1).map Block.length).sum = 65536 := by setup_source_rfl

private theorem tag_shape :
    (((sourceColumn ⟨8, by decide +kernel⟩).blocks.toList.drop 1).take 1) = [.affine 524288 58 0] := by setup_source_rfl

/-- The source tag stays equal to the original split table identifier. -/
theorem source_split_tag_get (index : Fin 524288) :
    ((SourceCaptureTheta.columns[8]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val) = some 58 := by
  have selected := getFromBlocks_window (sourceColumn ⟨8, by decide +kernel⟩).blocks.toList 1 1 65536 index.val
    tag_offset (by rw [tag_shape]; exact index.isLt)
  change ((SourceCaptureTheta.columns[8]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val) = _ at selected
  have bound : index.val < (Block.affine 524288 58 0).length := index.isLt
  rw [selected, tag_shape, getFromBlocks, if_pos bound]
  exact constant_affine_get _ _ _ index.isLt

/-- All three source keys equal their original native literal-tree keys. -/
theorem source_split_keys_match (column : Fin 3) (index : Fin 524288) :
    (((SourceCaptureTheta.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val)).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.columns[column.val]).value index.val := by
  fin_cases column
  · rw [source_split_first_get, Option.getD_some,
      Airbender.Keccak.Split.Native.Fixed.Proofs.theta_split_first_value ⟨index.val, index.isLt⟩]
  · rw [source_split_second_get, Option.getD_some,
      Airbender.Keccak.Split.Native.Fixed.Proofs.theta_split_second_value ⟨index.val, index.isLt⟩]
  · rw [source_split_shift_get, Option.getD_some,
      Airbender.Keccak.Split.Native.Fixed.Proofs.theta_split_shift_value ⟨index.val, index.isLt⟩]

end Airbender.Setup.SourceCaptureThetaProofs
