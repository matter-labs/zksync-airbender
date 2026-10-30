import Airbender.Proofs.FullUnsigned.SourceColumnRanges
import Airbender.Proofs.FullUnsigned.Source.Chi
import Airbender.Proofs.Keccak.SplitChiOutputs
import Airbender.Proofs.Tables.PeriodicColumns

namespace Airbender.Setup.SourceCaptureChiProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
-- Each retained prefix has at most 256 blocks. Its templates have at most 256 values.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private noncomputable def output3Blocks : List Block :=
  (((SourceCaptureChi.columns[8]?).getD ({ blocks := #[] } : Column)).blocks.toList).take 256

private noncomputable def output4Blocks : List Block :=
  (((SourceCaptureChi.columns[9]?).getD ({ blocks := #[] } : Column)).blocks.toList).take 16

private def output3Bits (block : Nat) : Nat :=
  if block / 16 < 8 then 4 else if block / 16 < 12 then 3 else if block / 16 < 14 then 2 else 1

private def output3Period (block : Nat) : Nat := 2 ^ output3Bits block

private def output3Block (block : Nat) : Block :=
  if block / 16 = 15 then .affine 4096 (block % 16) 0 else
    .periodic (4096 / output3Period block) 0 (Array.ofFn fun low : Fin (output3Period block) =>
      (block % 16) ^^^ ((15 ^^^ (block / 16)) &&& low.val))

private theorem output3_shape : output3Blocks = (List.range 256).map output3Block := by
  setup_source_rfl


private theorem output3_period_info : ∀ block : Fin 256,
    0 < output3Period block.val ∧ (4096 / output3Period block.val) * output3Period block.val = 4096 ∧
      (15 ^^^ (block.val / 16)) < output3Period block.val ∧ (15 ^^^ (block.val / 16)) < 16 := by
  decide +kernel


private def output4Block (block : Nat) : Block :=
  .periodic 256 0 (Array.ofFn fun low : Fin 256 =>
    block ^^^ ((15 ^^^ (low.val % 16)) &&& (low.val / 16)))

private theorem output4_entry_0 : output4Blocks[0]? = some (output4Block 0) := by
  setup_source_rfl

private theorem output4_entry_1 : output4Blocks[1]? = some (output4Block 1) := by
  setup_source_rfl

private theorem output4_entry_2 : output4Blocks[2]? = some (output4Block 2) := by
  setup_source_rfl

private theorem output4_entry_3 : output4Blocks[3]? = some (output4Block 3) := by
  setup_source_rfl

private theorem output4_entry_4 : output4Blocks[4]? = some (output4Block 4) := by
  setup_source_rfl

private theorem output4_entry_5 : output4Blocks[5]? = some (output4Block 5) := by
  setup_source_rfl

private theorem output4_entry_6 : output4Blocks[6]? = some (output4Block 6) := by
  setup_source_rfl

private theorem output4_entry_7 : output4Blocks[7]? = some (output4Block 7) := by
  setup_source_rfl

private theorem output4_entry_8 : output4Blocks[8]? = some (output4Block 8) := by
  setup_source_rfl

private theorem output4_entry_9 : output4Blocks[9]? = some (output4Block 9) := by
  setup_source_rfl

private theorem output4_entry_10 : output4Blocks[10]? = some (output4Block 10) := by
  setup_source_rfl

private theorem output4_entry_11 : output4Blocks[11]? = some (output4Block 11) := by
  setup_source_rfl

private theorem output4_entry_12 : output4Blocks[12]? = some (output4Block 12) := by
  setup_source_rfl

private theorem output4_entry_13 : output4Blocks[13]? = some (output4Block 13) := by
  setup_source_rfl

private theorem output4_entry_14 : output4Blocks[14]? = some (output4Block 14) := by
  setup_source_rfl

private theorem output4_entry_15 : output4Blocks[15]? = some (output4Block 15) := by
  setup_source_rfl

private theorem output4_entry (block : Fin 16) :
    output4Blocks[block.val]? = some (output4Block block.val) := by
  fin_cases block
  · change output4Blocks[0]? = some (output4Block 0)
    exact output4_entry_0
  · change output4Blocks[1]? = some (output4Block 1)
    exact output4_entry_1
  · change output4Blocks[2]? = some (output4Block 2)
    exact output4_entry_2
  · change output4Blocks[3]? = some (output4Block 3)
    exact output4_entry_3
  · change output4Blocks[4]? = some (output4Block 4)
    exact output4_entry_4
  · change output4Blocks[5]? = some (output4Block 5)
    exact output4_entry_5
  · change output4Blocks[6]? = some (output4Block 6)
    exact output4_entry_6
  · change output4Blocks[7]? = some (output4Block 7)
    exact output4_entry_7
  · change output4Blocks[8]? = some (output4Block 8)
    exact output4_entry_8
  · change output4Blocks[9]? = some (output4Block 9)
    exact output4_entry_9
  · change output4Blocks[10]? = some (output4Block 10)
    exact output4_entry_10
  · change output4Blocks[11]? = some (output4Block 11)
    exact output4_entry_11
  · change output4Blocks[12]? = some (output4Block 12)
    exact output4_entry_12
  · change output4Blocks[13]? = some (output4Block 13)
    exact output4_entry_13
  · change output4Blocks[14]? = some (output4Block 14)
    exact output4_entry_14
  · change output4Blocks[15]? = some (output4Block 15)
    exact output4_entry_15


private theorem output3_block_lengths : ∀ block ∈ output3Blocks, block.length = 4096 := by
  rw [output3_shape]
  intro block member
  obtain ⟨number, within, rfl⟩ := List.mem_map.mp member
  have bound : number < 256 := List.mem_range.mp within
  by_cases constant : number / 16 = 15
  · simp only [output3Block, if_pos constant, Block.length]
  · simp only [output3Block, if_neg constant, Block.length, Array.size_ofFn]
    exact (output3_period_info ⟨number, bound⟩).2.1

private theorem output4_block_lengths : ∀ block ∈ output4Blocks, block.length = 65536 := by
  decide +kernel

private theorem output3_length : (output3Blocks.map Block.length).sum = 1048576 := by
  setup_source_rfl

private theorem output4_length : (output4Blocks.map Block.length).sum = 1048576 := by
  setup_source_rfl

private theorem masked_mod (mask value bits : Nat) (bound : mask < 2 ^ bits) :
    mask &&& (value % 2 ^ bits) = mask &&& value := by
  have sample := Nat.and_mod_two_pow (a := mask) (b := value) (n := bits)
  have small : mask &&& value < 2 ^ bits := lt_of_le_of_lt Nat.and_le_left bound
  rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt bound] at sample
  exact sample.symm

private theorem output3_block_get (block : Fin 256) (offset : Fin 4096) :
    (output3Block block.val).get? offset.val =
      some ((block.val % 16) ^^^ ((15 ^^^ (block.val / 16)) &&& (offset.val % 16))) := by
  by_cases constant : block.val / 16 = 15
  · rw [output3Block, if_pos constant, constant_affine_get _ _ _ offset.isLt]
    simp [constant]
  · rw [output3Block, if_neg constant]
    have info := output3_period_info block
    have sampled := periodic_get
      (Array.ofFn fun low : Fin (output3Period block.val) =>
        (block.val % 16) ^^^ ((15 ^^^ (block.val / 16)) &&& low.val))
      (4096 / output3Period block.val) 0 offset.val
      (by simpa only [Array.size_ofFn] using info.1)
      (by simpa only [Array.size_ofFn, info.2.1] using offset.isLt)
    have projected := masked_mod (15 ^^^ (block.val / 16)) offset.val (output3Bits block.val) info.2.2.1
    have nibble := masked_mod (15 ^^^ (block.val / 16)) offset.val 4 info.2.2.2
    change (15 ^^^ (block.val / 16)) &&& (offset.val % 16) = (15 ^^^ (block.val / 16)) &&& offset.val at nibble
    simpa [output3Period, projected, nibble] using sampled

private theorem output4_block_get (block : Fin 16) (offset : Fin 65536) :
    (Block.periodic 256 0 (Array.ofFn fun low : Fin 256 =>
      block.val ^^^ ((15 ^^^ (low.val % 16)) &&& (low.val / 16)))).get? offset.val =
      some (block.val ^^^ ((15 ^^^ (offset.val % 16)) &&& (offset.val / 16 % 16))) := by
  have sampled := periodic_get
    (Array.ofFn fun low : Fin 256 => block.val ^^^ ((15 ^^^ (low.val % 16)) &&& (low.val / 16)))
    256 0 offset.val (by simp) (by simpa only [Array.size_ofFn] using offset.isLt)
  have low : offset.val % 256 % 16 = offset.val % 16 := by omega
  have high : offset.val % 256 / 16 = offset.val / 16 % 16 := by omega
  simpa [low, high] using sampled

private theorem source_output3_prefix (index : Fin 1048576) :
    ((SourceCaptureChi.columns[8]?).getD ({ blocks := #[] } : Column)).get? index.val = getFromBlocks output3Blocks index.val := by
  apply getFromBlocks_take
  change index.val < (output3Blocks.map Block.length).sum
  rw [output3_length]
  exact index.isLt

private theorem source_output4_prefix (index : Fin 1048576) :
    ((SourceCaptureChi.columns[9]?).getD ({ blocks := #[] } : Column)).get? index.val = getFromBlocks output4Blocks index.val := by
  apply getFromBlocks_take
  change index.val < (output4Blocks.map Block.length).sum
  rw [output4_length]
  exact index.isLt

/-- Every retained source field for chi output three has its exact nibble value. -/
theorem source_output3_get (index : Fin 1048576) :
    ((SourceCaptureChi.columns[8]?).getD ({ blocks := #[] } : Column)).get? index.val =
      some ((index.val / 4096 % 16) ^^^ ((15 ^^^ (index.val / 65536 % 16)) &&& (index.val % 16))) := by
  rw [source_output3_prefix, uniform4096_get _ output3_block_lengths, output3_shape]
  have bound : index.val / 4096 < 256 := by omega
  simp only [List.getElem?_map, List.getElem?_range, bound, Option.map_some, Option.bind_some]
  have selected := output3_block_get ⟨index.val / 4096, bound⟩
    ⟨index.val % 4096, Nat.mod_lt _ (by decide)⟩
  have low : index.val % 4096 % 16 = index.val % 16 := by omega
  have high : index.val / 4096 / 16 = index.val / 65536 % 16 := by omega
  simpa only [low, high] using selected

/-- Every retained source field for chi output four has its exact nibble value. -/
theorem source_output4_get (index : Fin 1048576) :
    ((SourceCaptureChi.columns[9]?).getD ({ blocks := #[] } : Column)).get? index.val =
      some ((index.val / 65536 % 16) ^^^ ((15 ^^^ (index.val % 16)) &&& (index.val / 16 % 16))) := by
  rw [source_output4_prefix, uniform65536_get _ output4_block_lengths]
  have bound : index.val / 65536 < 16 := by omega
  rw [output4_entry ⟨index.val / 65536, bound⟩]
  simp only [Option.bind_some]
  have selected := output4_block_get ⟨index.val / 65536, bound⟩
    ⟨index.val % 65536, Nat.mod_lt _ (by decide)⟩
  have low : index.val % 65536 % 16 = index.val % 16 := by omega
  have high : index.val % 65536 / 16 % 16 = index.val / 16 % 16 := by omega
  simpa only [output4Block, low, high, Nat.mod_eq_of_lt bound] using selected

/-- Source output three matches its original canonical generic-table field. -/
theorem source_output3_matches (index : Fin 1048576) :
    ((SourceCaptureChi.columns[8]?).getD ({ blocks := #[] } : Column)).get? index.val =
      Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[8].get? index.val := by
  have present := Airbender.Keccak.Split.Native.Fixed.Proofs.chi5_output_get (⟨3, by decide +kernel⟩ : Fin 5) index
  have value := Airbender.Keccak.Split.Native.Fixed.Proofs.chi5_output_value (⟨3, by decide +kernel⟩ : Fin 5) index
  change Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[8].get? index.val = some _ at present
  conv_rhs at value => norm_num
  change (Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[8].get? index.val).getD 0 =
    (index.val / 4096 % 16) ^^^ ((15 ^^^ (index.val / 65536 % 16)) &&& (index.val % 16)) at value
  rw [present, Option.getD_some] at value
  exact (source_output3_get index).trans ((present.trans (congrArg some value)).symm)

/-- Source output four matches its original canonical generic-table field. -/
theorem source_output4_matches (index : Fin 1048576) :
    ((SourceCaptureChi.columns[9]?).getD ({ blocks := #[] } : Column)).get? index.val =
      Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[9].get? index.val := by
  have present := Airbender.Keccak.Split.Native.Fixed.Proofs.chi5_output_get (⟨4, by decide +kernel⟩ : Fin 5) index
  have value := Airbender.Keccak.Split.Native.Fixed.Proofs.chi5_output_value (⟨4, by decide +kernel⟩ : Fin 5) index
  change Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[9].get? index.val = some _ at present
  conv_rhs at value => norm_num
  change (Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[9].get? index.val).getD 0 =
    (index.val / 65536 % 16) ^^^ ((15 ^^^ (index.val % 16)) &&& (index.val / 16 % 16)) at value
  rw [present, Option.getD_some] at value
  exact (source_output4_get index).trans ((present.trans (congrArg some value)).symm)

end Airbender.Setup.SourceCaptureChiProofs
