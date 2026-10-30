import Airbender.Proofs.FullUnsigned.SourceBlockScaling
import Airbender.Proofs.FullUnsigned.Source.Chi
import Airbender.Proofs.Keccak.SplitChiOutputs

namespace Airbender.Setup.SourceCaptureChiProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
-- The source has 40 arithmetic templates and 4,096 distinct chunk positions.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private noncomputable def output2Blocks : List Block :=
  (((SourceCaptureChi.columns[7]?).getD ({ blocks := #[] } : Column)).blocks.toList).take 567

private noncomputable def sourceBinding : SourceBank.ColumnBinding :=
  (SourceCaptureChi.columnBindings[7]'(by change 7 < 11; decide +kernel)).1

private def sourceIds : List Nat := SourceCaptureChi.entries_2871.take 567

private def output2Chunk (id : Nat) : ChunkBlock :=
  match id with
  | 1 => .periodic 16 1 #[0]
  | 2 => .periodic 8 2 #[1, 0]
  | 3 => .periodic 4 4 #[2, 3, 0, 1]
  | 4 => .periodic 4 4 #[3, 2, 1, 0]
  | 5 => .periodic 4 1 #[4]
  | 6 => .periodic 4 1 #[0]
  | 7 => .periodic 4 (-4) #[12, 13, 14, 15]
  | 8 => .periodic 4 1 #[12]
  | 9 => .periodic 4 1 #[8]
  | 10 => .constant 1 5
  | 11 => .constant 1 4
  | 12 => .constant 1 7
  | 13 => .constant 1 6
  | 14 => .constant 1 1
  | 15 => .constant 1 0
  | 16 => .constant 1 3
  | 17 => .constant 1 2
  | 18 => .constant 1 13
  | 19 => .constant 1 12
  | 20 => .constant 1 15
  | 21 => .constant 1 14
  | 22 => .constant 1 9
  | 23 => .constant 1 8
  | 24 => .constant 1 11
  | 25 => .constant 1 10
  | 26 => .periodic 4 (-2) #[6, 7]
  | 27 => .periodic 8 (-2) #[14, 15]
  | 28 => .periodic 4 (-2) #[14, 15]
  | 29 => .periodic 8 (-1) #[7]
  | 30 => .periodic 8 (-1) #[15]
  | 31 => .periodic 8 1 #[8]
  | 32 => .periodic 8 1 #[0]
  | 33 => .periodic 4 2 #[9, 8]
  | 34 => .periodic 4 2 #[1, 0]
  | 35 => .periodic 4 (-1) #[11]
  | 36 => .periodic 4 (-1) #[15]
  | 37 => .periodic 4 (-1) #[3]
  | 38 => .periodic 4 (-1) #[7]
  | 39 => .periodic 4 (-4) #[13, 12, 15, 14]
  | 40 => .periodic 16 (-1) #[15]
  | _ => .constant 0 0

private theorem source_shape : output2Blocks = sourceIds.map sourceBinding.blocks := by
  setup_source_rfl

private theorem ids_range : ∀ id ∈ sourceIds, 1 ≤ id ∧ id ≤ 40 := by
  decide +kernel

private theorem template_1 : sourceBinding.blocks 1 = (output2Chunk 1).expand := by
  setup_source_rfl

private theorem template_2 : sourceBinding.blocks 2 = (output2Chunk 2).expand := by
  setup_source_rfl

private theorem template_3 : sourceBinding.blocks 3 = (output2Chunk 3).expand := by
  setup_source_rfl

private theorem template_4 : sourceBinding.blocks 4 = (output2Chunk 4).expand := by
  setup_source_rfl

private theorem template_5 : sourceBinding.blocks 5 = (output2Chunk 5).expand := by
  setup_source_rfl

private theorem template_6 : sourceBinding.blocks 6 = (output2Chunk 6).expand := by
  setup_source_rfl

private theorem template_7 : sourceBinding.blocks 7 = (output2Chunk 7).expand := by
  setup_source_rfl

private theorem template_8 : sourceBinding.blocks 8 = (output2Chunk 8).expand := by
  setup_source_rfl

private theorem template_9 : sourceBinding.blocks 9 = (output2Chunk 9).expand := by
  setup_source_rfl

private theorem template_10 : sourceBinding.blocks 10 = (output2Chunk 10).expand := by
  setup_source_rfl

private theorem template_11 : sourceBinding.blocks 11 = (output2Chunk 11).expand := by
  setup_source_rfl

private theorem template_12 : sourceBinding.blocks 12 = (output2Chunk 12).expand := by
  setup_source_rfl

private theorem template_13 : sourceBinding.blocks 13 = (output2Chunk 13).expand := by
  setup_source_rfl

private theorem template_14 : sourceBinding.blocks 14 = (output2Chunk 14).expand := by
  setup_source_rfl

private theorem template_15 : sourceBinding.blocks 15 = (output2Chunk 15).expand := by
  setup_source_rfl

private theorem template_16 : sourceBinding.blocks 16 = (output2Chunk 16).expand := by
  setup_source_rfl

private theorem template_17 : sourceBinding.blocks 17 = (output2Chunk 17).expand := by
  setup_source_rfl

private theorem template_18 : sourceBinding.blocks 18 = (output2Chunk 18).expand := by
  setup_source_rfl

private theorem template_19 : sourceBinding.blocks 19 = (output2Chunk 19).expand := by
  setup_source_rfl

private theorem template_20 : sourceBinding.blocks 20 = (output2Chunk 20).expand := by
  setup_source_rfl

private theorem template_21 : sourceBinding.blocks 21 = (output2Chunk 21).expand := by
  setup_source_rfl

private theorem template_22 : sourceBinding.blocks 22 = (output2Chunk 22).expand := by
  setup_source_rfl

private theorem template_23 : sourceBinding.blocks 23 = (output2Chunk 23).expand := by
  setup_source_rfl

private theorem template_24 : sourceBinding.blocks 24 = (output2Chunk 24).expand := by
  setup_source_rfl

private theorem template_25 : sourceBinding.blocks 25 = (output2Chunk 25).expand := by
  setup_source_rfl

private theorem template_26 : sourceBinding.blocks 26 = (output2Chunk 26).expand := by
  setup_source_rfl

private theorem template_27 : sourceBinding.blocks 27 = (output2Chunk 27).expand := by
  setup_source_rfl

private theorem template_28 : sourceBinding.blocks 28 = (output2Chunk 28).expand := by
  setup_source_rfl

private theorem template_29 : sourceBinding.blocks 29 = (output2Chunk 29).expand := by
  setup_source_rfl

private theorem template_30 : sourceBinding.blocks 30 = (output2Chunk 30).expand := by
  setup_source_rfl

private theorem template_31 : sourceBinding.blocks 31 = (output2Chunk 31).expand := by
  setup_source_rfl

private theorem template_32 : sourceBinding.blocks 32 = (output2Chunk 32).expand := by
  setup_source_rfl

private theorem template_33 : sourceBinding.blocks 33 = (output2Chunk 33).expand := by
  setup_source_rfl

private theorem template_34 : sourceBinding.blocks 34 = (output2Chunk 34).expand := by
  setup_source_rfl

private theorem template_35 : sourceBinding.blocks 35 = (output2Chunk 35).expand := by
  setup_source_rfl

private theorem template_36 : sourceBinding.blocks 36 = (output2Chunk 36).expand := by
  setup_source_rfl

private theorem template_37 : sourceBinding.blocks 37 = (output2Chunk 37).expand := by
  setup_source_rfl

private theorem template_38 : sourceBinding.blocks 38 = (output2Chunk 38).expand := by
  setup_source_rfl

private theorem template_39 : sourceBinding.blocks 39 = (output2Chunk 39).expand := by
  setup_source_rfl

private theorem template_40 : sourceBinding.blocks 40 = (output2Chunk 40).expand := by
  setup_source_rfl

private theorem template_shape (id : Fin 40) :
    sourceBinding.blocks (id.val + 1) = (output2Chunk (id.val + 1)).expand := by
  fin_cases id
  · exact template_1
  · exact template_2
  · exact template_3
  · exact template_4
  · exact template_5
  · exact template_6
  · exact template_7
  · exact template_8
  · exact template_9
  · exact template_10
  · exact template_11
  · exact template_12
  · exact template_13
  · exact template_14
  · exact template_15
  · exact template_16
  · exact template_17
  · exact template_18
  · exact template_19
  · exact template_20
  · exact template_21
  · exact template_22
  · exact template_23
  · exact template_24
  · exact template_25
  · exact template_26
  · exact template_27
  · exact template_28
  · exact template_29
  · exact template_30
  · exact template_31
  · exact template_32
  · exact template_33
  · exact template_34
  · exact template_35
  · exact template_36
  · exact template_37
  · exact template_38
  · exact template_39
  · exact template_40

private theorem source_expansion :
    output2Blocks = (sourceIds.map output2Chunk).map ChunkBlock.expand := by
  rw [source_shape, List.map_map]
  apply List.map_congr_left
  intro id member
  have bounds := ids_range id member
  have shape := template_shape ⟨id - 1, by omega⟩
  simpa only [show id - 1 + 1 = id by omega, Function.comp_apply] using shape

private def output2Expected (index : Nat) : Nat :=
  (index % 16) ^^^ ((15 ^^^ (index / 16 % 16)) &&& (index / 256 % 16))

private theorem compact_checked :
    checkBlockRows output2Expected 0 ((sourceIds.map output2Chunk).map ChunkBlock.compact) = true := by
  decide +kernel

private theorem compact_length :
    (((sourceIds.map output2Chunk).map ChunkBlock.compact).map Block.length).sum = 4096 := by
  setup_source_rfl

private theorem source_length : (output2Blocks.map Block.length).sum = 1048576 := by
  rw [source_expansion, List.map_map]
  simp only [Function.comp_def, ChunkBlock.expand_length]
  rw [List.sum_map_mul_left]
  change 256 * (((sourceIds.map output2Chunk).map ChunkBlock.compact).map Block.length).sum = _
  rw [compact_length]

/-- Every physical source row for chi output two has its exact nibble value. -/
theorem source_output2_get (index : Fin 1048576) :
    ((SourceCaptureChi.columns[7]?).getD ({ blocks := #[] } : Column)).get? index.val =
      some ((index.val / 256 % 16) ^^^
        ((15 ^^^ (index.val / 4096 % 16)) &&& (index.val / 65536 % 16))) := by
  change getFromBlocks _ index.val = _
  rw [getFromBlocks_take _ 567 index.val (by change index.val < (output2Blocks.map Block.length).sum; rw [source_length]; exact index.isLt)]
  change getFromBlocks output2Blocks index.val = _
  rw [source_expansion, getFromBlocks_expand]
  have checked := checkBlockRows_sound output2Expected _ 0 (index.val / 256) compact_checked
    (by rw [compact_length]; omega)
  simpa only [Nat.zero_add, output2Expected, Nat.div_div_eq_div_mul] using checked

/-- Source output two matches its original canonical generic-table field. -/
theorem source_output2_matches (index : Fin 1048576) :
    ((SourceCaptureChi.columns[7]?).getD ({ blocks := #[] } : Column)).get? index.val =
      Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[7].get? index.val := by
  have present := Airbender.Keccak.Split.Native.Fixed.Proofs.chi5_output_get
    (⟨2, by decide +kernel⟩ : Fin 5) index
  have value := Airbender.Keccak.Split.Native.Fixed.Proofs.chi5_output_value
    (⟨2, by decide +kernel⟩ : Fin 5) index
  change Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[7].get? index.val = some _ at present
  conv_rhs at value => norm_num
  change (Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[7].get? index.val).getD 0 =
    (index.val / 256 % 16) ^^^ ((15 ^^^ (index.val / 4096 % 16)) &&& (index.val / 65536 % 16)) at value
  rw [present, Option.getD_some] at value
  exact (source_output2_get index).trans ((present.trans (congrArg some value)).symm)

end Airbender.Setup.SourceCaptureChiProofs
