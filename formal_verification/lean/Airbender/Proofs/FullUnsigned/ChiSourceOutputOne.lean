import Airbender.Proofs.FullUnsigned.ChiSourceCycle1
import Airbender.Proofs.FullUnsigned.SourceBlockCycles
import Airbender.Proofs.FullUnsigned.SourceScaledChunks
import Airbender.Proofs.FullUnsigned.ChiSourceController
import Airbender.Proofs.Keccak.SplitChiOutputs

namespace Airbender.Setup.SourceCaptureChiProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
-- The source uses 53 arithmetic templates. Each compact cycle has 4,096 rows.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private noncomputable def sourceBinding : SourceBank.ColumnBinding :=
  (SourceCaptureChi.columnBindings[6]'(by change 6 < 11; decide +kernel)).1

private def output1Chunk (id : Nat) : ChunkBlock :=
  match id with
  | 1 => .periodic 16 (0) #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  | 2 => .periodic 8 (0) #[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  | 3 => .periodic 4 (0) #[2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  | 4 => .periodic 4 (0) #[3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  | 5 => .periodic 4 (0) #[4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11]
  | 6 => .periodic 4 (0) #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  | 7 => .constant 1 5
  | 8 => .constant 1 4
  | 9 => .constant 1 7
  | 10 => .constant 1 6
  | 11 => .constant 1 1
  | 12 => .constant 1 0
  | 13 => .constant 1 3
  | 14 => .constant 1 2
  | 15 => .constant 1 13
  | 16 => .constant 1 12
  | 17 => .constant 1 15
  | 18 => .constant 1 14
  | 19 => .constant 1 9
  | 20 => .constant 1 8
  | 21 => .constant 1 11
  | 22 => .constant 1 10
  | 23 => .periodic 4 (1) #[4]
  | 24 => .periodic 4 (1) #[0]
  | 25 => .periodic 4 (1) #[12]
  | 26 => .periodic 4 (1) #[8]
  | 27 => .periodic 8 (2) #[1, 0]
  | 28 => .periodic 16 (1) #[0]
  | 29 => .periodic 4 (-2) #[6, 7]
  | 30 => .periodic 8 (-2) #[14, 15]
  | 31 => .periodic 4 (-2) #[14, 15]
  | 32 => .periodic 4 (-4) #[12, 13, 14, 15]
  | 33 => .periodic 4 (4) #[2, 3, 0, 1]
  | 34 => .periodic 8 (-1) #[7]
  | 35 => .periodic 8 (-1) #[15]
  | 36 => .periodic 4 (4) #[3, 2, 1, 0]
  | 37 => .periodic 8 (0) #[8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]
  | 38 => .periodic 8 (0) #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  | 39 => .periodic 4 (0) #[9, 8, 11, 10, 13, 12, 15, 14, 1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]
  | 40 => .periodic 4 (0) #[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  | 41 => .periodic 8 (1) #[8]
  | 42 => .periodic 8 (1) #[0]
  | 43 => .periodic 4 (-1) #[11]
  | 44 => .periodic 4 (-1) #[15]
  | 45 => .periodic 4 (-1) #[3]
  | 46 => .periodic 4 (-1) #[7]
  | 47 => .periodic 4 (2) #[9, 8]
  | 48 => .periodic 4 (2) #[1, 0]
  | 49 => .periodic 4 (0) #[12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3]
  | 50 => .periodic 4 (0) #[8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]
  | 51 => .periodic 4 (-4) #[13, 12, 15, 14]
  | 52 => .periodic 16 (-1) #[15]
  | 53 => .periodic 17 (0) #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  | _ => .constant 0 0

private def frontChunks : List ChunkBlock := ChiSourceCycle1.front.map output1Chunk
private def cycleChunks : List ChunkBlock := ChiSourceCycle1.cycle.map output1Chunk
private def tailChunks : List ChunkBlock := (ChiSourceCycle1.tail.take 435).map output1Chunk
private noncomputable def restBlocks : List Block := (ChiSourceCycle1.tail.drop 435).map sourceBinding.blocks
private def arithmeticChunks : List ChunkBlock :=
  frontChunks ++ (List.replicate 15 cycleChunks).flatten ++ tailChunks

private theorem front_range : ∀ id ∈ ChiSourceCycle1.front, 1 ≤ id ∧ id ≤ 53 := by decide +kernel
private theorem cycle_range : ∀ id ∈ ChiSourceCycle1.cycle, 1 ≤ id ∧ id ≤ 53 := by decide +kernel
private theorem tail_range : ∀ id ∈ ChiSourceCycle1.tail.take 435, 1 ≤ id ∧ id ≤ 53 := by decide +kernel

private theorem template_1 : sourceBinding.blocks 1 = (output1Chunk 1).expandBy 16 := by
  setup_source_rfl

private theorem template_2 : sourceBinding.blocks 2 = (output1Chunk 2).expandBy 16 := by
  setup_source_rfl

private theorem template_3 : sourceBinding.blocks 3 = (output1Chunk 3).expandBy 16 := by
  setup_source_rfl

private theorem template_4 : sourceBinding.blocks 4 = (output1Chunk 4).expandBy 16 := by
  setup_source_rfl

private theorem template_5 : sourceBinding.blocks 5 = (output1Chunk 5).expandBy 16 := by
  setup_source_rfl

private theorem template_6 : sourceBinding.blocks 6 = (output1Chunk 6).expandBy 16 := by
  setup_source_rfl

private theorem template_7 : sourceBinding.blocks 7 = (output1Chunk 7).expandBy 16 := by
  setup_source_rfl

private theorem template_8 : sourceBinding.blocks 8 = (output1Chunk 8).expandBy 16 := by
  setup_source_rfl

private theorem template_9 : sourceBinding.blocks 9 = (output1Chunk 9).expandBy 16 := by
  setup_source_rfl

private theorem template_10 : sourceBinding.blocks 10 = (output1Chunk 10).expandBy 16 := by
  setup_source_rfl

private theorem template_11 : sourceBinding.blocks 11 = (output1Chunk 11).expandBy 16 := by
  setup_source_rfl

private theorem template_12 : sourceBinding.blocks 12 = (output1Chunk 12).expandBy 16 := by
  setup_source_rfl

private theorem template_13 : sourceBinding.blocks 13 = (output1Chunk 13).expandBy 16 := by
  setup_source_rfl

private theorem template_14 : sourceBinding.blocks 14 = (output1Chunk 14).expandBy 16 := by
  setup_source_rfl

private theorem template_15 : sourceBinding.blocks 15 = (output1Chunk 15).expandBy 16 := by
  setup_source_rfl

private theorem template_16 : sourceBinding.blocks 16 = (output1Chunk 16).expandBy 16 := by
  setup_source_rfl

private theorem template_17 : sourceBinding.blocks 17 = (output1Chunk 17).expandBy 16 := by
  setup_source_rfl

private theorem template_18 : sourceBinding.blocks 18 = (output1Chunk 18).expandBy 16 := by
  setup_source_rfl

private theorem template_19 : sourceBinding.blocks 19 = (output1Chunk 19).expandBy 16 := by
  setup_source_rfl

private theorem template_20 : sourceBinding.blocks 20 = (output1Chunk 20).expandBy 16 := by
  setup_source_rfl

private theorem template_21 : sourceBinding.blocks 21 = (output1Chunk 21).expandBy 16 := by
  setup_source_rfl

private theorem template_22 : sourceBinding.blocks 22 = (output1Chunk 22).expandBy 16 := by
  setup_source_rfl

private theorem template_23 : sourceBinding.blocks 23 = (output1Chunk 23).expandBy 16 := by
  setup_source_rfl

private theorem template_24 : sourceBinding.blocks 24 = (output1Chunk 24).expandBy 16 := by
  setup_source_rfl

private theorem template_25 : sourceBinding.blocks 25 = (output1Chunk 25).expandBy 16 := by
  setup_source_rfl

private theorem template_26 : sourceBinding.blocks 26 = (output1Chunk 26).expandBy 16 := by
  setup_source_rfl

private theorem template_27 : sourceBinding.blocks 27 = (output1Chunk 27).expandBy 16 := by
  setup_source_rfl

private theorem template_28 : sourceBinding.blocks 28 = (output1Chunk 28).expandBy 16 := by
  setup_source_rfl

private theorem template_29 : sourceBinding.blocks 29 = (output1Chunk 29).expandBy 16 := by
  setup_source_rfl

private theorem template_30 : sourceBinding.blocks 30 = (output1Chunk 30).expandBy 16 := by
  setup_source_rfl

private theorem template_31 : sourceBinding.blocks 31 = (output1Chunk 31).expandBy 16 := by
  setup_source_rfl

private theorem template_32 : sourceBinding.blocks 32 = (output1Chunk 32).expandBy 16 := by
  setup_source_rfl

private theorem template_33 : sourceBinding.blocks 33 = (output1Chunk 33).expandBy 16 := by
  setup_source_rfl

private theorem template_34 : sourceBinding.blocks 34 = (output1Chunk 34).expandBy 16 := by
  setup_source_rfl

private theorem template_35 : sourceBinding.blocks 35 = (output1Chunk 35).expandBy 16 := by
  setup_source_rfl

private theorem template_36 : sourceBinding.blocks 36 = (output1Chunk 36).expandBy 16 := by
  setup_source_rfl

private theorem template_37 : sourceBinding.blocks 37 = (output1Chunk 37).expandBy 16 := by
  setup_source_rfl

private theorem template_38 : sourceBinding.blocks 38 = (output1Chunk 38).expandBy 16 := by
  setup_source_rfl

private theorem template_39 : sourceBinding.blocks 39 = (output1Chunk 39).expandBy 16 := by
  setup_source_rfl

private theorem template_40 : sourceBinding.blocks 40 = (output1Chunk 40).expandBy 16 := by
  setup_source_rfl

private theorem template_41 : sourceBinding.blocks 41 = (output1Chunk 41).expandBy 16 := by
  setup_source_rfl

private theorem template_42 : sourceBinding.blocks 42 = (output1Chunk 42).expandBy 16 := by
  setup_source_rfl

private theorem template_43 : sourceBinding.blocks 43 = (output1Chunk 43).expandBy 16 := by
  setup_source_rfl

private theorem template_44 : sourceBinding.blocks 44 = (output1Chunk 44).expandBy 16 := by
  setup_source_rfl

private theorem template_45 : sourceBinding.blocks 45 = (output1Chunk 45).expandBy 16 := by
  setup_source_rfl

private theorem template_46 : sourceBinding.blocks 46 = (output1Chunk 46).expandBy 16 := by
  setup_source_rfl

private theorem template_47 : sourceBinding.blocks 47 = (output1Chunk 47).expandBy 16 := by
  setup_source_rfl

private theorem template_48 : sourceBinding.blocks 48 = (output1Chunk 48).expandBy 16 := by
  setup_source_rfl

private theorem template_49 : sourceBinding.blocks 49 = (output1Chunk 49).expandBy 16 := by
  setup_source_rfl

private theorem template_50 : sourceBinding.blocks 50 = (output1Chunk 50).expandBy 16 := by
  setup_source_rfl

private theorem template_51 : sourceBinding.blocks 51 = (output1Chunk 51).expandBy 16 := by
  setup_source_rfl

private theorem template_52 : sourceBinding.blocks 52 = (output1Chunk 52).expandBy 16 := by
  setup_source_rfl

private theorem template_53 : sourceBinding.blocks 53 = (output1Chunk 53).expandBy 16 := by
  setup_source_rfl

private theorem template_shape (id : Fin 53) :
    sourceBinding.blocks (id.val + 1) = (output1Chunk (id.val + 1)).expandBy 16 := by
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
  · exact template_41
  · exact template_42
  · exact template_43
  · exact template_44
  · exact template_45
  · exact template_46
  · exact template_47
  · exact template_48
  · exact template_49
  · exact template_50
  · exact template_51
  · exact template_52
  · exact template_53

private theorem map_expansion (ids : List Nat) (range : ∀ id ∈ ids, 1 ≤ id ∧ id ≤ 53) :
    ids.map sourceBinding.blocks = (ids.map output1Chunk).map (ChunkBlock.expandBy 16) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro id member
  have bounds := range id member
  have shape := template_shape ⟨id - 1, by omega⟩
  simpa only [show id - 1 + 1 = id by omega, Function.comp_apply] using shape

private theorem source_column_binding :
    (SourceCaptureChi.columns[6]?).getD ({ blocks := #[] } : Column) = sourceBinding.column := by
  setup_source_rfl

private theorem binding_entries : sourceBinding.entries = SourceCaptureChi.entries_2804 := by
  simp only [sourceBinding, SourceCaptureChi.columnBindings, List.getElem_cons_zero, List.getElem_cons_succ]
  source_record_entries

private theorem source_blocks : sourceBinding.column.blocks.toList =
    arithmeticChunks.map (ChunkBlock.expandBy 16) ++ restBlocks := by
  simp only [SourceBank.ColumnBinding.column, List.toList_toArray]
  rw [binding_entries, ChiSourceCycle1.source_indices]
  simp only [List.map_append, List.map_flatten, List.map_replicate]
  have tailSplit : ChiSourceCycle1.tail =
      ChiSourceCycle1.tail.take 435 ++ ChiSourceCycle1.tail.drop 435 := (List.take_append_drop 435 _).symm
  rw [tailSplit, List.map_append, map_expansion _ front_range,
    map_expansion _ cycle_range, map_expansion _ tail_range]
  simp only [arithmeticChunks, frontChunks, cycleChunks, tailChunks, restBlocks,
    List.map_append, List.map_flatten, List.map_replicate, List.append_assoc]

private def frontBlocks : List Block := frontChunks.map ChunkBlock.compact
private def cycleBlocks : List Block := cycleChunks.map ChunkBlock.compact
private def tailBlocks : List Block := tailChunks.map ChunkBlock.compact

private def output1Expected (index : Nat) : Nat :=
  (index % 16) ^^^ ((15 ^^^ (index / 16 % 16)) &&& (index / 256 % 16))

private theorem front_length : (frontBlocks.map Block.length).sum = 256 := by setup_source_rfl
private theorem cycle_length : (cycleBlocks.map Block.length).sum = 4096 := by setup_source_rfl
private theorem tail_length : (tailBlocks.map Block.length).sum = 3840 := by setup_source_rfl

private theorem compact_blocks : arithmeticChunks.map ChunkBlock.compact =
    frontBlocks ++ (List.replicate 15 cycleBlocks).flatten ++ tailBlocks := by
  simp only [arithmeticChunks, frontBlocks, cycleBlocks, tailBlocks,
    List.map_append, List.map_flatten, List.map_replicate]

private theorem compact_length :
    ((arithmeticChunks.map ChunkBlock.compact).map Block.length).sum = 65536 := by
  rw [compact_blocks, List.map_append, List.sum_append, List.map_append, List.sum_append,
    repeated_blocks_length, front_length, cycle_length, tail_length]

private theorem front_checked : checkBlockRows output1Expected 0 frontBlocks = true := by decide +kernel
private theorem cycle_checked : checkBlockRows output1Expected 256 cycleBlocks = true := by decide +kernel
private theorem tail_checked : checkBlockRows output1Expected 256 tailBlocks = true := by decide +kernel

private theorem output1_periodic (a b : Nat) (same : a % 4096 = b % 4096) :
    output1Expected a = output1Expected b := by
  have low : a % 16 = b % 16 := by omega
  have middle : a / 16 % 16 = b / 16 % 16 := by omega
  have high : a / 256 % 16 = b / 256 % 16 := by omega
  simp only [output1Expected, low, middle, high]

private theorem compact_get (index : Fin 65536) :
    getFromBlocks (arithmeticChunks.map ChunkBlock.compact) index.val = some (output1Expected index.val) := by
  rw [compact_blocks]
  have checked := checked_cycle_rows output1Expected frontBlocks cycleBlocks tailBlocks [] 15 4096 index.val
    cycle_length front_checked (by rw [front_length]; exact cycle_checked)
    (by rw [front_length]; exact tail_checked) output1_periodic
    (by rw [front_length, tail_length]; exact index.isLt)
  simpa only [List.append_nil] using checked

/-- Every physical source row for chi output one has its exact nibble value. -/
theorem source_output1_get (index : Fin 1048576) :
    ((SourceCaptureChi.columns[6]?).getD ({ blocks := #[] } : Column)).get? index.val =
      some ((index.val / 16 % 16) ^^^ ((15 ^^^ (index.val / 256 % 16)) &&& (index.val / 4096 % 16))) := by
  rw [source_column_binding]
  change getFromBlocks sourceBinding.column.blocks.toList index.val = _
  rw [source_blocks, getFromBlocks_append_left _ _ _ (by
    rw [expanded_blocks_length, compact_length]; exact index.isLt), getFromBlocks_expandBy _ (by decide +kernel)]
  have selected := compact_get ⟨index.val / 16, by omega⟩
  simpa only [output1Expected, Nat.div_div_eq_div_mul] using selected

/-- Source output one matches its original canonical generic-table field. -/
theorem source_output1_matches (index : Fin 1048576) :
    ((SourceCaptureChi.columns[6]?).getD ({ blocks := #[] } : Column)).get? index.val =
      Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[6].get? index.val := by
  have present := Airbender.Keccak.Split.Native.Fixed.Proofs.chi5_output_get
    (⟨1, by decide +kernel⟩ : Fin 5) index
  have value := Airbender.Keccak.Split.Native.Fixed.Proofs.chi5_output_value
    (⟨1, by decide +kernel⟩ : Fin 5) index
  change Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[6].get? index.val = some _ at present
  conv_rhs at value => norm_num
  change (Airbender.Keccak.Split.Native.Fixed.chi5Generic.columns[6].get? index.val).getD 0 =
    (index.val / 16 % 16) ^^^ ((15 ^^^ (index.val / 256 % 16)) &&& (index.val / 4096 % 16)) at value
  rw [present, Option.getD_some] at value
  exact (source_output1_get index).trans ((present.trans (congrArg some value)).symm)

end Airbender.Setup.SourceCaptureChiProofs
