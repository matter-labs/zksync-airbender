import Airbender.Proofs.Tables.PeriodicColumns
import Airbender.Proofs.FullUnsigned.SourceUniformChunks
import Airbender.Proofs.FullUnsigned.SourceBlockWindows
import Airbender.Proofs.FullUnsigned.SourceBlockTrimming
import Airbender.Proofs.FullUnsigned.Source.Parity
import Airbender.Proofs.Keccak.SplitXor5Inputs
import Airbender.Proofs.Keccak.SplitXor5Outputs

namespace Airbender.Setup.SourceCaptureParityProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
-- Five direct template rules cover the complete XOR-five input domain.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private noncomputable def sourceColumn (column : Fin 8) : Column :=
  (SourceCaptureParity.columns[column.val]?).getD ⟨#[]⟩
private def keySkip (column : Fin 5) : Nat :=
  match column.val with
  | 0 => 52
  | 1 => 16
  | 2 => 161
  | 3 => 58
  | _ => 11
private def keyCount (column : Fin 5) : Nat := if column.val = 2 ∨ column.val = 3 then 256 else if column.val = 4 then 16 else 1
private def keyOffset (column : Fin 5) : Nat := if column.val = 4 then 122 else 0
private noncomputable def keyWindow (column : Fin 5) : List Block :=
  ((sourceColumn ⟨column.val, by omega⟩).blocks.toList.drop (keySkip column)).take (keyCount column)
private theorem key_prefix_lengths (column : Fin 5) :
    (((sourceColumn ⟨column.val, by omega⟩).blocks.toList.take (keySkip column)).map Block.length).sum =
      65780 - keyOffset column := by fin_cases column <;> setup_source_rfl
private theorem key_window_lengths (column : Fin 5) :
    ((keyWindow column).map Block.length).sum = 1048576 + keyOffset column := by
  fin_cases column <;> setup_source_rfl

private theorem source_key_window (column : Fin 5) (index : Fin 1048576) :
    ((SourceCaptureParity.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? (65780 + index.val) =
      getFromBlocks (keyWindow column) (keyOffset column + index.val) := by
  have offsetBound : keyOffset column ≤ 65780 := by fin_cases column <;> decide +kernel
  have selected := getFromBlocks_window (sourceColumn ⟨column.val, by omega⟩).blocks.toList
    (keySkip column) (keyCount column) (65780 - keyOffset column) (keyOffset column + index.val)
    (key_prefix_lengths column) (by change keyOffset column + index.val < ((keyWindow column).map Block.length).sum; rw [key_window_lengths]; omega)
  have position : 65780 - keyOffset column + (keyOffset column + index.val) = 65780 + index.val := by omega
  rw [position] at selected
  exact selected

private def secondPattern : Array Nat := (List.ofFn fun index : Fin 256 => index.val / 16).toArray
private theorem second_size : secondPattern.size = 256 := by simp only [secondPattern, List.size_toArray, List.length_ofFn]
private theorem key_zero_shape : keyWindow ⟨0, by decide +kernel⟩ = [.periodic 65536 0 (Array.range 16)] := by setup_source_rfl
private theorem key_one_shape : keyWindow ⟨1, by decide +kernel⟩ = [.periodic 4096 0 secondPattern] := by setup_source_rfl
private theorem key_two_shape : keyWindow ⟨2, by decide +kernel⟩ =
    List.replicate 256 (.periodic 16 1 (Array.replicate 256 0)) := by setup_source_rfl
private theorem key_three_shape : keyWindow ⟨3, by decide +kernel⟩ =
    (List.range 256).map (fun digit => Block.affine 4096 (digit % 16) 0) := by setup_source_rfl
private theorem key_four_shape : keyWindow ⟨4, by decide +kernel⟩ =
    .affine 65658 0 0 :: (List.range 15).map (fun digit => Block.affine 65536 (digit + 1) 0) := by setup_source_rfl

private theorem first_get (index : Fin 1048576) : getFromBlocks (keyWindow ⟨0, by decide +kernel⟩) index.val = some (index.val % 16) := by
  rw [key_zero_shape, getFromBlocks, if_pos (by simpa only [Block.length, Array.size_range] using index.isLt)]
  simpa only [Array.size_range, Array.getElem_range, Int.natCast_zero, Nat.zero_mul, Nat.add_zero] using
    periodic_get (Array.range 16) 65536 0 index.val (by simp) (by simpa only [Array.size_range] using index.isLt)

private theorem second_get (index : Fin 1048576) : getFromBlocks (keyWindow ⟨1, by decide +kernel⟩) index.val = some (index.val / 16 % 16) := by
  rw [key_one_shape, getFromBlocks, if_pos (by rw [Block.length, second_size]; exact index.isLt)]
  have sampled := periodic_get secondPattern 4096 0 index.val (by rw [second_size]; decide +kernel)
    (by rw [second_size]; exact index.isLt)
  simp only [second_size, Int.natCast_zero, Nat.zero_mul, Nat.add_zero] at sampled
  have cell : secondPattern[index.val % 256]'(by rw [second_size]; omega) = index.val % 256 / 16 := by
    simp only [secondPattern, List.getElem_toArray, List.getElem_ofFn]
  rw [cell] at sampled
  have residue : index.val % 256 / 16 = index.val / 16 % 16 := by omega
  simpa only [residue] using sampled

private theorem third_get (index : Fin 1048576) : getFromBlocks (keyWindow ⟨2, by decide +kernel⟩) index.val = some (index.val / 256 % 16) := by
  rw [key_two_shape]
  have lengths : ∀ block ∈ List.replicate 256 (Block.periodic 16 1 (Array.replicate 256 0)), block.length = 4096 := by
    intro block member
    rw [(List.mem_replicate.mp member).2]
    rfl
  rw [uniform_blocks_get _ 4096 (by decide +kernel) lengths,
    List.getElem?_replicate_of_lt (by omega : index.val / 4096 < 256), Option.bind_some]
  have sampled := periodic_get (Array.replicate 256 0) 16 1 (index.val % 4096) (by simp)
    (by simpa only [Array.size_replicate] using Nat.mod_lt index.val (by decide +kernel : 0 < 4096))
  have residue : index.val % 4096 / 256 = index.val / 256 % 16 := by omega
  simpa only [Array.size_replicate, Array.getElem_replicate, Int.natCast_one, Nat.one_mul, Nat.zero_add, residue] using sampled

private theorem fourth_get (index : Fin 1048576) : getFromBlocks (keyWindow ⟨3, by decide +kernel⟩) index.val = some (index.val / 4096 % 16) := by
  rw [key_three_shape]
  have lengths : ∀ block ∈ (List.range 256).map (fun digit => Block.affine 4096 (digit % 16) 0), block.length = 4096 := by
    intro block member
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    rfl
  rw [uniform_blocks_get _ 4096 (by decide +kernel) lengths]
  simp only [List.getElem?_map, List.getElem?_range, (by omega : index.val / 4096 < 256), Option.map_some, Option.bind_some]
  exact constant_affine_get _ _ _ (Nat.mod_lt _ (by decide +kernel))

private theorem fifth_get (index : Fin 1048576) : getFromBlocks (keyWindow ⟨4, by decide +kernel⟩) (122 + index.val) = some (index.val / 65536 % 16) := by
  rw [key_four_shape, skip_constant_head 65658 0 122 index.val _ (by decide +kernel)]
  change getFromBlocks ((List.range 16).map (fun digit => Block.affine 65536 digit 0)) index.val = _
  have lengths : ∀ block ∈ (List.range 16).map (fun digit => Block.affine 65536 digit 0), block.length = 65536 := by
    intro block member
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    rfl
  rw [uniform_blocks_get _ 65536 (by decide +kernel) lengths]
  have high : index.val / 65536 < 16 := by omega
  simp only [List.getElem?_map, List.getElem?_range, high, Option.map_some, Option.bind_some, Nat.mod_eq_of_lt high]
  exact constant_affine_get _ _ _ (Nat.mod_lt _ (by decide +kernel))

/-- The five stored source keys are their original bounded base-sixteen digits. -/
theorem source_xor_keys_get (column : Fin 5) (index : Fin 1048576) :
    ((SourceCaptureParity.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? (65780 + index.val) =
      some (index.val / 16 ^ column.val % 16) := by
  rw [source_key_window]
  fin_cases column
  · simpa [keyOffset] using first_get index
  · simpa [keyOffset] using second_get index
  · simpa [keyOffset] using third_get index
  · simpa [keyOffset] using fourth_get index
  · simpa [keyOffset] using fifth_get index

/-- Every source XOR-five key equals its complete original native key. -/
theorem source_xor_keys_match (column : Fin 5) (index : Fin 1048576) :
    (((SourceCaptureParity.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? (65780 + index.val)).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.columnParityXor5.columns[column.val]).value index.val := by
  rw [source_xor_keys_get, Option.getD_some,
    Airbender.Keccak.Split.Native.Fixed.Proofs.xor5_key_values column index.val]

private theorem padding_offset : (((sourceColumn ⟨6, by decide +kernel⟩).blocks.toList.take 26).map Block.length).sum = 65658 := by setup_source_rfl
private theorem padding_shape : ((sourceColumn ⟨6, by decide +kernel⟩).blocks.toList.drop 26).take 1 = [.affine 4128646 0 0] := by setup_source_rfl
private theorem tag_offset : (((sourceColumn ⟨7, by decide +kernel⟩).blocks.toList.take 3).map Block.length).sum = 65780 := by setup_source_rfl
private theorem tag_shape : ((sourceColumn ⟨7, by decide +kernel⟩).blocks.toList.drop 3).take 1 = [.affine 1048576 64 0] := by setup_source_rfl

/-- The complete original XOR-five source padding field stays zero. -/
theorem source_xor_padding_get (index : Fin 1048576) :
    ((SourceCaptureParity.columns[6]?).getD ({ blocks := #[] } : Column)).get? (65780 + index.val) = some 0 := by
  have selected := getFromBlocks_window (sourceColumn ⟨6, by decide +kernel⟩).blocks.toList 26 1 65658 (122 + index.val)
    padding_offset (by rw [padding_shape]; change 122 + index.val < 4128646; omega)
  have position : 65658 + (122 + index.val) = 65780 + index.val := by omega
  rw [position, padding_shape] at selected
  change getFromBlocks (sourceColumn ⟨6, by decide +kernel⟩).blocks.toList (65780 + index.val) = _
  rw [selected, getFromBlocks, if_pos (by change 122 + index.val < 4128646; omega)]
  exact constant_affine_get _ _ _ (by omega)

/-- The original XOR-five tag is exact on the full source arithmetic region. -/
theorem source_xor_tag_get (index : Fin 1048576) :
    ((SourceCaptureParity.columns[7]?).getD ({ blocks := #[] } : Column)).get? (65780 + index.val) = some 64 := by
  have selected := getFromBlocks_window (sourceColumn ⟨7, by decide +kernel⟩).blocks.toList 3 1 65780 index.val
    tag_offset (by rw [tag_shape]; exact index.isLt)
  change getFromBlocks (sourceColumn ⟨7, by decide +kernel⟩).blocks.toList (65780 + index.val) = _
  rw [selected, tag_shape, getFromBlocks, Block.length, if_pos index.isLt]
  exact constant_affine_get _ _ _ index.isLt

/-- Both fixed source fields equal their complete original native values. -/
theorem source_xor_fixed_match (column : Fin 2) (index : Fin 1048576) :
    (((SourceCaptureParity.columns[6 + column.val]?).getD ({ blocks := #[] } : Column)).get? (65780 + index.val)).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.columnParityXor5.columns[6 + column.val]).value index.val := by
  fin_cases column
  · exact (congrArg (fun value : Option Nat => value.getD 0) (source_xor_padding_get index)).trans
      (Airbender.Keccak.Split.Native.Fixed.Proofs.xor5_fixed_values index.val).1.symm
  · exact (congrArg (fun value : Option Nat => value.getD 0) (source_xor_tag_get index)).trans
      (Airbender.Keccak.Split.Native.Fixed.Proofs.xor5_fixed_values index.val).2.symm

end Airbender.Setup.SourceCaptureParityProofs
