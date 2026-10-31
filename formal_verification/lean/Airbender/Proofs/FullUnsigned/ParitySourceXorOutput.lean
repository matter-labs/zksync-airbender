import Airbender.Proofs.FullUnsigned.ThetaSourceLowZero
import Airbender.Proofs.FullUnsigned.ParityOutputGroup0
import Airbender.Proofs.FullUnsigned.ParityOutputGroup1
import Airbender.Proofs.FullUnsigned.ParityOutputGroup2
import Airbender.Proofs.FullUnsigned.ParityOutputGroup3
import Airbender.Proofs.FullUnsigned.ParityOutputGroup4
import Airbender.Proofs.FullUnsigned.ParityOutputGroup5
import Airbender.Proofs.FullUnsigned.ParityOutputGroup6
import Airbender.Proofs.FullUnsigned.ParityOutputGroup7
import Airbender.Proofs.FullUnsigned.ParityOutputGroup8
import Airbender.Proofs.FullUnsigned.ParityOutputGroup9
import Airbender.Proofs.FullUnsigned.ParityOutputGroup10
import Airbender.Proofs.FullUnsigned.ParityOutputGroup11
import Airbender.Proofs.FullUnsigned.ParityOutputGroup12
import Airbender.Proofs.FullUnsigned.ParityOutputGroup13
import Airbender.Proofs.FullUnsigned.ParityOutputGroup14
import Airbender.Proofs.FullUnsigned.ParityOutputGroup15
import Airbender.Proofs.FullUnsigned.ParityOutputGroup16
import Airbender.Proofs.FullUnsigned.ParitySourcePrefixRead
import Airbender.Proofs.Keccak.SplitXor5Outputs

namespace Airbender.Setup.SourceCaptureParityProofs
open Airbender.Setup.Proofs OutputIntervals
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private noncomputable def sourceColumn : Column := (SourceCaptureParity.columns[5]?).getD ⟨#[]⟩
private noncomputable def frontBlocks : List Block := blocks 0
private noncomputable def backBlocks : List Block := blocks 66
private noncomputable def outputBlocks : List Block :=
  blocks 1 ++ (blocks 2 ++ (blocks 3 ++ (blocks 4 ++ (blocks 5 ++ (blocks 6 ++ (blocks 7 ++ (blocks 8 ++ (blocks 9 ++ (blocks 10 ++ (blocks 11 ++ (blocks 12 ++ (blocks 13 ++ (blocks 14 ++ (blocks 15 ++ (blocks 16 ++ (blocks 17 ++ (blocks 18 ++ (blocks 19 ++ (blocks 20 ++ (blocks 21 ++ (blocks 22 ++ (blocks 23 ++ (blocks 24 ++ (blocks 25 ++ (blocks 26 ++ (blocks 27 ++ (blocks 28 ++ (blocks 29 ++ (blocks 30 ++ (blocks 31 ++ (blocks 32 ++ (blocks 33 ++ (blocks 34 ++ (blocks 35 ++ (blocks 36 ++ (blocks 37 ++ (blocks 38 ++ (blocks 39 ++ (blocks 40 ++ (blocks 41 ++ (blocks 42 ++ (blocks 43 ++ (blocks 44 ++ (blocks 45 ++ (blocks 46 ++ (blocks 47 ++ (blocks 48 ++ (blocks 49 ++ (blocks 50 ++ (blocks 51 ++ (blocks 52 ++ (blocks 53 ++ (blocks 54 ++ (blocks 55 ++ (blocks 56 ++ (blocks 57 ++ (blocks 58 ++ (blocks 59 ++ (blocks 60 ++ (blocks 61 ++ (blocks 62 ++ (blocks 63 ++ (blocks 64 ++ (blocks 65))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem source_column_binding : sourceColumn = binding.column := by
  simp only [binding, SourceCaptureParity.columnBindings, List.getElem_cons_zero, List.getElem_cons_succ]
  rfl
private theorem binding_entries : binding.entries = SourceCaptureParity.entries_3282 := by
  simp only [binding, SourceCaptureParity.columnBindings, List.getElem_cons_zero, List.getElem_cons_succ]
  source_record_entries

private theorem output_shape : outputBlocks =
    ((List.range 65).map fun index => blocks (index + 1)).flatten := by low_source_kernel_rfl

private theorem chunks_indexed : ParityOutputPartition.chunks =
    [(ParityOutputPartition.chunks[0]?).getD []] ++
      (List.range 65).map (fun index => (ParityOutputPartition.chunks[index + 1]?).getD []) ++
      [(ParityOutputPartition.chunks[66]?).getD []] := by low_source_kernel_rfl

private theorem source_partition : sourceColumn.blocks.toList = frontBlocks ++ outputBlocks ++ backBlocks := by
  rw [source_column_binding]
  simp only [SourceBank.ColumnBinding.column, List.toList_toArray]
  rw [binding_entries, ParityOutputPartition.matches, List.map_flatten]
  have indexed := congrArg (fun parts : List (List Nat) => (parts.map (List.map binding.blocks)).flatten) chunks_indexed
  simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.map_map, Function.comp_def] at indexed
  rw [indexed]
  rw [output_shape]
  rfl

private theorem front_length : (frontBlocks.map Block.length).sum = 65781 := by decide +kernel
private theorem front_final_zero : getFromBlocks frontBlocks 65780 = some 0 := by decide +kernel

private theorem all_parts (index : Fin 65) : IntervalFact (1 + index.val) := by
  fin_cases index
  · change IntervalFact 1
    exact OutputGroup0.facts (⟨0, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 2
    exact OutputGroup0.facts (⟨1, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 3
    exact OutputGroup0.facts (⟨2, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 4
    exact OutputGroup0.facts (⟨3, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 5
    exact OutputGroup1.facts (⟨0, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 6
    exact OutputGroup1.facts (⟨1, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 7
    exact OutputGroup1.facts (⟨2, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 8
    exact OutputGroup1.facts (⟨3, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 9
    exact OutputGroup2.facts (⟨0, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 10
    exact OutputGroup2.facts (⟨1, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 11
    exact OutputGroup2.facts (⟨2, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 12
    exact OutputGroup2.facts (⟨3, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 13
    exact OutputGroup3.facts (⟨0, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 14
    exact OutputGroup3.facts (⟨1, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 15
    exact OutputGroup3.facts (⟨2, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 16
    exact OutputGroup3.facts (⟨3, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 17
    exact OutputGroup4.facts (⟨0, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 18
    exact OutputGroup4.facts (⟨1, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 19
    exact OutputGroup4.facts (⟨2, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 20
    exact OutputGroup4.facts (⟨3, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 21
    exact OutputGroup5.facts (⟨0, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 22
    exact OutputGroup5.facts (⟨1, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 23
    exact OutputGroup5.facts (⟨2, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 24
    exact OutputGroup5.facts (⟨3, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 25
    exact OutputGroup6.facts (⟨0, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 26
    exact OutputGroup6.facts (⟨1, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 27
    exact OutputGroup6.facts (⟨2, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 28
    exact OutputGroup6.facts (⟨3, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 29
    exact OutputGroup7.facts (⟨0, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 30
    exact OutputGroup7.facts (⟨1, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 31
    exact OutputGroup7.facts (⟨2, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 32
    exact OutputGroup7.facts (⟨3, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 33
    exact OutputGroup8.facts (⟨0, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 34
    exact OutputGroup8.facts (⟨1, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 35
    exact OutputGroup8.facts (⟨2, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 36
    exact OutputGroup8.facts (⟨3, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 37
    exact OutputGroup9.facts (⟨0, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 38
    exact OutputGroup9.facts (⟨1, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 39
    exact OutputGroup9.facts (⟨2, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 40
    exact OutputGroup9.facts (⟨3, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 41
    exact OutputGroup10.facts (⟨0, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 42
    exact OutputGroup10.facts (⟨1, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 43
    exact OutputGroup10.facts (⟨2, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 44
    exact OutputGroup10.facts (⟨3, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 45
    exact OutputGroup11.facts (⟨0, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 46
    exact OutputGroup11.facts (⟨1, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 47
    exact OutputGroup11.facts (⟨2, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 48
    exact OutputGroup11.facts (⟨3, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 49
    exact OutputGroup12.facts (⟨0, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 50
    exact OutputGroup12.facts (⟨1, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 51
    exact OutputGroup12.facts (⟨2, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 52
    exact OutputGroup12.facts (⟨3, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 53
    exact OutputGroup13.facts (⟨0, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 54
    exact OutputGroup13.facts (⟨1, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 55
    exact OutputGroup13.facts (⟨2, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 56
    exact OutputGroup13.facts (⟨3, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 57
    exact OutputGroup14.facts (⟨0, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 58
    exact OutputGroup14.facts (⟨1, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 59
    exact OutputGroup14.facts (⟨2, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 60
    exact OutputGroup14.facts (⟨3, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 61
    exact OutputGroup15.facts (⟨0, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 62
    exact OutputGroup15.facts (⟨1, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 63
    exact OutputGroup15.facts (⟨2, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 64
    exact OutputGroup15.facts (⟨3, by decide +kernel⟩ : Fin 4)
  · change IntervalFact 65
    exact OutputGroup16.facts (⟨0, by decide +kernel⟩ : Fin 1)

private theorem output_length : (outputBlocks.map Block.length).sum = 1048575 := by
  have length0 := (all_parts (⟨0, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 1).map Block.length).sum = 16383 at length0
  have length1 := (all_parts (⟨1, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 2).map Block.length).sum = 16384 at length1
  have length2 := (all_parts (⟨2, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 3).map Block.length).sum = 16384 at length2
  have length3 := (all_parts (⟨3, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 4).map Block.length).sum = 16384 at length3
  have length4 := (all_parts (⟨4, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 5).map Block.length).sum = 16384 at length4
  have length5 := (all_parts (⟨5, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 6).map Block.length).sum = 16384 at length5
  have length6 := (all_parts (⟨6, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 7).map Block.length).sum = 16384 at length6
  have length7 := (all_parts (⟨7, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 8).map Block.length).sum = 16384 at length7
  have length8 := (all_parts (⟨8, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 9).map Block.length).sum = 16384 at length8
  have length9 := (all_parts (⟨9, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 10).map Block.length).sum = 16368 at length9
  have length10 := (all_parts (⟨10, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 11).map Block.length).sum = 16384 at length10
  have length11 := (all_parts (⟨11, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 12).map Block.length).sum = 16384 at length11
  have length12 := (all_parts (⟨12, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 13).map Block.length).sum = 16384 at length12
  have length13 := (all_parts (⟨13, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 14).map Block.length).sum = 16384 at length13
  have length14 := (all_parts (⟨14, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 15).map Block.length).sum = 16384 at length14
  have length15 := (all_parts (⟨15, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 16).map Block.length).sum = 16384 at length15
  have length16 := (all_parts (⟨16, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 17).map Block.length).sum = 16384 at length16
  have length17 := (all_parts (⟨17, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 18).map Block.length).sum = 16384 at length17
  have length18 := (all_parts (⟨18, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 19).map Block.length).sum = 16384 at length18
  have length19 := (all_parts (⟨19, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 20).map Block.length).sum = 16384 at length19
  have length20 := (all_parts (⟨20, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 21).map Block.length).sum = 16384 at length20
  have length21 := (all_parts (⟨21, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 22).map Block.length).sum = 16384 at length21
  have length22 := (all_parts (⟨22, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 23).map Block.length).sum = 16384 at length22
  have length23 := (all_parts (⟨23, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 24).map Block.length).sum = 16384 at length23
  have length24 := (all_parts (⟨24, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 25).map Block.length).sum = 16384 at length24
  have length25 := (all_parts (⟨25, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 26).map Block.length).sum = 16384 at length25
  have length26 := (all_parts (⟨26, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 27).map Block.length).sum = 16384 at length26
  have length27 := (all_parts (⟨27, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 28).map Block.length).sum = 16384 at length27
  have length28 := (all_parts (⟨28, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 29).map Block.length).sum = 16384 at length28
  have length29 := (all_parts (⟨29, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 30).map Block.length).sum = 16384 at length29
  have length30 := (all_parts (⟨30, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 31).map Block.length).sum = 16384 at length30
  have length31 := (all_parts (⟨31, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 32).map Block.length).sum = 16384 at length31
  have length32 := (all_parts (⟨32, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 33).map Block.length).sum = 16384 at length32
  have length33 := (all_parts (⟨33, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 34).map Block.length).sum = 16384 at length33
  have length34 := (all_parts (⟨34, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 35).map Block.length).sum = 16384 at length34
  have length35 := (all_parts (⟨35, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 36).map Block.length).sum = 16384 at length35
  have length36 := (all_parts (⟨36, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 37).map Block.length).sum = 16384 at length36
  have length37 := (all_parts (⟨37, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 38).map Block.length).sum = 16384 at length37
  have length38 := (all_parts (⟨38, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 39).map Block.length).sum = 16384 at length38
  have length39 := (all_parts (⟨39, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 40).map Block.length).sum = 16384 at length39
  have length40 := (all_parts (⟨40, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 41).map Block.length).sum = 16384 at length40
  have length41 := (all_parts (⟨41, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 42).map Block.length).sum = 16384 at length41
  have length42 := (all_parts (⟨42, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 43).map Block.length).sum = 16384 at length42
  have length43 := (all_parts (⟨43, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 44).map Block.length).sum = 16384 at length43
  have length44 := (all_parts (⟨44, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 45).map Block.length).sum = 16384 at length44
  have length45 := (all_parts (⟨45, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 46).map Block.length).sum = 16384 at length45
  have length46 := (all_parts (⟨46, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 47).map Block.length).sum = 16384 at length46
  have length47 := (all_parts (⟨47, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 48).map Block.length).sum = 16384 at length47
  have length48 := (all_parts (⟨48, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 49).map Block.length).sum = 16384 at length48
  have length49 := (all_parts (⟨49, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 50).map Block.length).sum = 16384 at length49
  have length50 := (all_parts (⟨50, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 51).map Block.length).sum = 16384 at length50
  have length51 := (all_parts (⟨51, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 52).map Block.length).sum = 16384 at length51
  have length52 := (all_parts (⟨52, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 53).map Block.length).sum = 16384 at length52
  have length53 := (all_parts (⟨53, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 54).map Block.length).sum = 16384 at length53
  have length54 := (all_parts (⟨54, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 55).map Block.length).sum = 16384 at length54
  have length55 := (all_parts (⟨55, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 56).map Block.length).sum = 16384 at length55
  have length56 := (all_parts (⟨56, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 57).map Block.length).sum = 16384 at length56
  have length57 := (all_parts (⟨57, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 58).map Block.length).sum = 16384 at length57
  have length58 := (all_parts (⟨58, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 59).map Block.length).sum = 16384 at length58
  have length59 := (all_parts (⟨59, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 60).map Block.length).sum = 16384 at length59
  have length60 := (all_parts (⟨60, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 61).map Block.length).sum = 16384 at length60
  have length61 := (all_parts (⟨61, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 62).map Block.length).sum = 16384 at length61
  have length62 := (all_parts (⟨62, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 63).map Block.length).sum = 16384 at length62
  have length63 := (all_parts (⟨63, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 64).map Block.length).sum = 16384 at length63
  have length64 := (all_parts (⟨64, by decide +kernel⟩ : Fin 65)).1
  change ((blocks 65).map Block.length).sum = 16 at length64
  simp only [outputBlocks, List.map_append, List.sum_append, length0, length1, length2, length3, length4, length5, length6, length7, length8, length9, length10, length11, length12, length13, length14, length15, length16, length17, length18, length19, length20, length21, length22, length23, length24, length25, length26, length27, length28, length29, length30, length31, length32, length33, length34, length35, length36, length37, length38, length39, length40, length41, length42, length43, length44, length45, length46, length47, length48, length49, length50, length51, length52, length53, length54, length55, length56, length57, length58, length59, length60, length61, length62, length63, length64, Nat.reduceAdd]

private theorem output_checked : checkBlockRows expected 65781 outputBlocks = true := by
  unfold outputBlocks
  have closed0 := all_parts (⟨0, by decide +kernel⟩ : Fin 65)
  change ((blocks 1).map Block.length).sum = 16383 ∧ checkBlockRows expected 65781 (blocks 1) = true at closed0
  rw [checkBlockRows_append, closed0.2, Bool.true_and, closed0.1]
  norm_num only [Nat.reduceAdd]
  have closed1 := all_parts (⟨1, by decide +kernel⟩ : Fin 65)
  change ((blocks 2).map Block.length).sum = 16384 ∧ checkBlockRows expected 82164 (blocks 2) = true at closed1
  rw [checkBlockRows_append, closed1.2, Bool.true_and, closed1.1]
  norm_num only [Nat.reduceAdd]
  have closed2 := all_parts (⟨2, by decide +kernel⟩ : Fin 65)
  change ((blocks 3).map Block.length).sum = 16384 ∧ checkBlockRows expected 98548 (blocks 3) = true at closed2
  rw [checkBlockRows_append, closed2.2, Bool.true_and, closed2.1]
  norm_num only [Nat.reduceAdd]
  have closed3 := all_parts (⟨3, by decide +kernel⟩ : Fin 65)
  change ((blocks 4).map Block.length).sum = 16384 ∧ checkBlockRows expected 114932 (blocks 4) = true at closed3
  rw [checkBlockRows_append, closed3.2, Bool.true_and, closed3.1]
  norm_num only [Nat.reduceAdd]
  have closed4 := all_parts (⟨4, by decide +kernel⟩ : Fin 65)
  change ((blocks 5).map Block.length).sum = 16384 ∧ checkBlockRows expected 131316 (blocks 5) = true at closed4
  rw [checkBlockRows_append, closed4.2, Bool.true_and, closed4.1]
  norm_num only [Nat.reduceAdd]
  have closed5 := all_parts (⟨5, by decide +kernel⟩ : Fin 65)
  change ((blocks 6).map Block.length).sum = 16384 ∧ checkBlockRows expected 147700 (blocks 6) = true at closed5
  rw [checkBlockRows_append, closed5.2, Bool.true_and, closed5.1]
  norm_num only [Nat.reduceAdd]
  have closed6 := all_parts (⟨6, by decide +kernel⟩ : Fin 65)
  change ((blocks 7).map Block.length).sum = 16384 ∧ checkBlockRows expected 164084 (blocks 7) = true at closed6
  rw [checkBlockRows_append, closed6.2, Bool.true_and, closed6.1]
  norm_num only [Nat.reduceAdd]
  have closed7 := all_parts (⟨7, by decide +kernel⟩ : Fin 65)
  change ((blocks 8).map Block.length).sum = 16384 ∧ checkBlockRows expected 180468 (blocks 8) = true at closed7
  rw [checkBlockRows_append, closed7.2, Bool.true_and, closed7.1]
  norm_num only [Nat.reduceAdd]
  have closed8 := all_parts (⟨8, by decide +kernel⟩ : Fin 65)
  change ((blocks 9).map Block.length).sum = 16384 ∧ checkBlockRows expected 196852 (blocks 9) = true at closed8
  rw [checkBlockRows_append, closed8.2, Bool.true_and, closed8.1]
  norm_num only [Nat.reduceAdd]
  have closed9 := all_parts (⟨9, by decide +kernel⟩ : Fin 65)
  change ((blocks 10).map Block.length).sum = 16368 ∧ checkBlockRows expected 213236 (blocks 10) = true at closed9
  rw [checkBlockRows_append, closed9.2, Bool.true_and, closed9.1]
  norm_num only [Nat.reduceAdd]
  have closed10 := all_parts (⟨10, by decide +kernel⟩ : Fin 65)
  change ((blocks 11).map Block.length).sum = 16384 ∧ checkBlockRows expected 229604 (blocks 11) = true at closed10
  rw [checkBlockRows_append, closed10.2, Bool.true_and, closed10.1]
  norm_num only [Nat.reduceAdd]
  have closed11 := all_parts (⟨11, by decide +kernel⟩ : Fin 65)
  change ((blocks 12).map Block.length).sum = 16384 ∧ checkBlockRows expected 245988 (blocks 12) = true at closed11
  rw [checkBlockRows_append, closed11.2, Bool.true_and, closed11.1]
  norm_num only [Nat.reduceAdd]
  have closed12 := all_parts (⟨12, by decide +kernel⟩ : Fin 65)
  change ((blocks 13).map Block.length).sum = 16384 ∧ checkBlockRows expected 262372 (blocks 13) = true at closed12
  rw [checkBlockRows_append, closed12.2, Bool.true_and, closed12.1]
  norm_num only [Nat.reduceAdd]
  have closed13 := all_parts (⟨13, by decide +kernel⟩ : Fin 65)
  change ((blocks 14).map Block.length).sum = 16384 ∧ checkBlockRows expected 278756 (blocks 14) = true at closed13
  rw [checkBlockRows_append, closed13.2, Bool.true_and, closed13.1]
  norm_num only [Nat.reduceAdd]
  have closed14 := all_parts (⟨14, by decide +kernel⟩ : Fin 65)
  change ((blocks 15).map Block.length).sum = 16384 ∧ checkBlockRows expected 295140 (blocks 15) = true at closed14
  rw [checkBlockRows_append, closed14.2, Bool.true_and, closed14.1]
  norm_num only [Nat.reduceAdd]
  have closed15 := all_parts (⟨15, by decide +kernel⟩ : Fin 65)
  change ((blocks 16).map Block.length).sum = 16384 ∧ checkBlockRows expected 311524 (blocks 16) = true at closed15
  rw [checkBlockRows_append, closed15.2, Bool.true_and, closed15.1]
  norm_num only [Nat.reduceAdd]
  have closed16 := all_parts (⟨16, by decide +kernel⟩ : Fin 65)
  change ((blocks 17).map Block.length).sum = 16384 ∧ checkBlockRows expected 327908 (blocks 17) = true at closed16
  rw [checkBlockRows_append, closed16.2, Bool.true_and, closed16.1]
  norm_num only [Nat.reduceAdd]
  have closed17 := all_parts (⟨17, by decide +kernel⟩ : Fin 65)
  change ((blocks 18).map Block.length).sum = 16384 ∧ checkBlockRows expected 344292 (blocks 18) = true at closed17
  rw [checkBlockRows_append, closed17.2, Bool.true_and, closed17.1]
  norm_num only [Nat.reduceAdd]
  have closed18 := all_parts (⟨18, by decide +kernel⟩ : Fin 65)
  change ((blocks 19).map Block.length).sum = 16384 ∧ checkBlockRows expected 360676 (blocks 19) = true at closed18
  rw [checkBlockRows_append, closed18.2, Bool.true_and, closed18.1]
  norm_num only [Nat.reduceAdd]
  have closed19 := all_parts (⟨19, by decide +kernel⟩ : Fin 65)
  change ((blocks 20).map Block.length).sum = 16384 ∧ checkBlockRows expected 377060 (blocks 20) = true at closed19
  rw [checkBlockRows_append, closed19.2, Bool.true_and, closed19.1]
  norm_num only [Nat.reduceAdd]
  have closed20 := all_parts (⟨20, by decide +kernel⟩ : Fin 65)
  change ((blocks 21).map Block.length).sum = 16384 ∧ checkBlockRows expected 393444 (blocks 21) = true at closed20
  rw [checkBlockRows_append, closed20.2, Bool.true_and, closed20.1]
  norm_num only [Nat.reduceAdd]
  have closed21 := all_parts (⟨21, by decide +kernel⟩ : Fin 65)
  change ((blocks 22).map Block.length).sum = 16384 ∧ checkBlockRows expected 409828 (blocks 22) = true at closed21
  rw [checkBlockRows_append, closed21.2, Bool.true_and, closed21.1]
  norm_num only [Nat.reduceAdd]
  have closed22 := all_parts (⟨22, by decide +kernel⟩ : Fin 65)
  change ((blocks 23).map Block.length).sum = 16384 ∧ checkBlockRows expected 426212 (blocks 23) = true at closed22
  rw [checkBlockRows_append, closed22.2, Bool.true_and, closed22.1]
  norm_num only [Nat.reduceAdd]
  have closed23 := all_parts (⟨23, by decide +kernel⟩ : Fin 65)
  change ((blocks 24).map Block.length).sum = 16384 ∧ checkBlockRows expected 442596 (blocks 24) = true at closed23
  rw [checkBlockRows_append, closed23.2, Bool.true_and, closed23.1]
  norm_num only [Nat.reduceAdd]
  have closed24 := all_parts (⟨24, by decide +kernel⟩ : Fin 65)
  change ((blocks 25).map Block.length).sum = 16384 ∧ checkBlockRows expected 458980 (blocks 25) = true at closed24
  rw [checkBlockRows_append, closed24.2, Bool.true_and, closed24.1]
  norm_num only [Nat.reduceAdd]
  have closed25 := all_parts (⟨25, by decide +kernel⟩ : Fin 65)
  change ((blocks 26).map Block.length).sum = 16384 ∧ checkBlockRows expected 475364 (blocks 26) = true at closed25
  rw [checkBlockRows_append, closed25.2, Bool.true_and, closed25.1]
  norm_num only [Nat.reduceAdd]
  have closed26 := all_parts (⟨26, by decide +kernel⟩ : Fin 65)
  change ((blocks 27).map Block.length).sum = 16384 ∧ checkBlockRows expected 491748 (blocks 27) = true at closed26
  rw [checkBlockRows_append, closed26.2, Bool.true_and, closed26.1]
  norm_num only [Nat.reduceAdd]
  have closed27 := all_parts (⟨27, by decide +kernel⟩ : Fin 65)
  change ((blocks 28).map Block.length).sum = 16384 ∧ checkBlockRows expected 508132 (blocks 28) = true at closed27
  rw [checkBlockRows_append, closed27.2, Bool.true_and, closed27.1]
  norm_num only [Nat.reduceAdd]
  have closed28 := all_parts (⟨28, by decide +kernel⟩ : Fin 65)
  change ((blocks 29).map Block.length).sum = 16384 ∧ checkBlockRows expected 524516 (blocks 29) = true at closed28
  rw [checkBlockRows_append, closed28.2, Bool.true_and, closed28.1]
  norm_num only [Nat.reduceAdd]
  have closed29 := all_parts (⟨29, by decide +kernel⟩ : Fin 65)
  change ((blocks 30).map Block.length).sum = 16384 ∧ checkBlockRows expected 540900 (blocks 30) = true at closed29
  rw [checkBlockRows_append, closed29.2, Bool.true_and, closed29.1]
  norm_num only [Nat.reduceAdd]
  have closed30 := all_parts (⟨30, by decide +kernel⟩ : Fin 65)
  change ((blocks 31).map Block.length).sum = 16384 ∧ checkBlockRows expected 557284 (blocks 31) = true at closed30
  rw [checkBlockRows_append, closed30.2, Bool.true_and, closed30.1]
  norm_num only [Nat.reduceAdd]
  have closed31 := all_parts (⟨31, by decide +kernel⟩ : Fin 65)
  change ((blocks 32).map Block.length).sum = 16384 ∧ checkBlockRows expected 573668 (blocks 32) = true at closed31
  rw [checkBlockRows_append, closed31.2, Bool.true_and, closed31.1]
  norm_num only [Nat.reduceAdd]
  have closed32 := all_parts (⟨32, by decide +kernel⟩ : Fin 65)
  change ((blocks 33).map Block.length).sum = 16384 ∧ checkBlockRows expected 590052 (blocks 33) = true at closed32
  rw [checkBlockRows_append, closed32.2, Bool.true_and, closed32.1]
  norm_num only [Nat.reduceAdd]
  have closed33 := all_parts (⟨33, by decide +kernel⟩ : Fin 65)
  change ((blocks 34).map Block.length).sum = 16384 ∧ checkBlockRows expected 606436 (blocks 34) = true at closed33
  rw [checkBlockRows_append, closed33.2, Bool.true_and, closed33.1]
  norm_num only [Nat.reduceAdd]
  have closed34 := all_parts (⟨34, by decide +kernel⟩ : Fin 65)
  change ((blocks 35).map Block.length).sum = 16384 ∧ checkBlockRows expected 622820 (blocks 35) = true at closed34
  rw [checkBlockRows_append, closed34.2, Bool.true_and, closed34.1]
  norm_num only [Nat.reduceAdd]
  have closed35 := all_parts (⟨35, by decide +kernel⟩ : Fin 65)
  change ((blocks 36).map Block.length).sum = 16384 ∧ checkBlockRows expected 639204 (blocks 36) = true at closed35
  rw [checkBlockRows_append, closed35.2, Bool.true_and, closed35.1]
  norm_num only [Nat.reduceAdd]
  have closed36 := all_parts (⟨36, by decide +kernel⟩ : Fin 65)
  change ((blocks 37).map Block.length).sum = 16384 ∧ checkBlockRows expected 655588 (blocks 37) = true at closed36
  rw [checkBlockRows_append, closed36.2, Bool.true_and, closed36.1]
  norm_num only [Nat.reduceAdd]
  have closed37 := all_parts (⟨37, by decide +kernel⟩ : Fin 65)
  change ((blocks 38).map Block.length).sum = 16384 ∧ checkBlockRows expected 671972 (blocks 38) = true at closed37
  rw [checkBlockRows_append, closed37.2, Bool.true_and, closed37.1]
  norm_num only [Nat.reduceAdd]
  have closed38 := all_parts (⟨38, by decide +kernel⟩ : Fin 65)
  change ((blocks 39).map Block.length).sum = 16384 ∧ checkBlockRows expected 688356 (blocks 39) = true at closed38
  rw [checkBlockRows_append, closed38.2, Bool.true_and, closed38.1]
  norm_num only [Nat.reduceAdd]
  have closed39 := all_parts (⟨39, by decide +kernel⟩ : Fin 65)
  change ((blocks 40).map Block.length).sum = 16384 ∧ checkBlockRows expected 704740 (blocks 40) = true at closed39
  rw [checkBlockRows_append, closed39.2, Bool.true_and, closed39.1]
  norm_num only [Nat.reduceAdd]
  have closed40 := all_parts (⟨40, by decide +kernel⟩ : Fin 65)
  change ((blocks 41).map Block.length).sum = 16384 ∧ checkBlockRows expected 721124 (blocks 41) = true at closed40
  rw [checkBlockRows_append, closed40.2, Bool.true_and, closed40.1]
  norm_num only [Nat.reduceAdd]
  have closed41 := all_parts (⟨41, by decide +kernel⟩ : Fin 65)
  change ((blocks 42).map Block.length).sum = 16384 ∧ checkBlockRows expected 737508 (blocks 42) = true at closed41
  rw [checkBlockRows_append, closed41.2, Bool.true_and, closed41.1]
  norm_num only [Nat.reduceAdd]
  have closed42 := all_parts (⟨42, by decide +kernel⟩ : Fin 65)
  change ((blocks 43).map Block.length).sum = 16384 ∧ checkBlockRows expected 753892 (blocks 43) = true at closed42
  rw [checkBlockRows_append, closed42.2, Bool.true_and, closed42.1]
  norm_num only [Nat.reduceAdd]
  have closed43 := all_parts (⟨43, by decide +kernel⟩ : Fin 65)
  change ((blocks 44).map Block.length).sum = 16384 ∧ checkBlockRows expected 770276 (blocks 44) = true at closed43
  rw [checkBlockRows_append, closed43.2, Bool.true_and, closed43.1]
  norm_num only [Nat.reduceAdd]
  have closed44 := all_parts (⟨44, by decide +kernel⟩ : Fin 65)
  change ((blocks 45).map Block.length).sum = 16384 ∧ checkBlockRows expected 786660 (blocks 45) = true at closed44
  rw [checkBlockRows_append, closed44.2, Bool.true_and, closed44.1]
  norm_num only [Nat.reduceAdd]
  have closed45 := all_parts (⟨45, by decide +kernel⟩ : Fin 65)
  change ((blocks 46).map Block.length).sum = 16384 ∧ checkBlockRows expected 803044 (blocks 46) = true at closed45
  rw [checkBlockRows_append, closed45.2, Bool.true_and, closed45.1]
  norm_num only [Nat.reduceAdd]
  have closed46 := all_parts (⟨46, by decide +kernel⟩ : Fin 65)
  change ((blocks 47).map Block.length).sum = 16384 ∧ checkBlockRows expected 819428 (blocks 47) = true at closed46
  rw [checkBlockRows_append, closed46.2, Bool.true_and, closed46.1]
  norm_num only [Nat.reduceAdd]
  have closed47 := all_parts (⟨47, by decide +kernel⟩ : Fin 65)
  change ((blocks 48).map Block.length).sum = 16384 ∧ checkBlockRows expected 835812 (blocks 48) = true at closed47
  rw [checkBlockRows_append, closed47.2, Bool.true_and, closed47.1]
  norm_num only [Nat.reduceAdd]
  have closed48 := all_parts (⟨48, by decide +kernel⟩ : Fin 65)
  change ((blocks 49).map Block.length).sum = 16384 ∧ checkBlockRows expected 852196 (blocks 49) = true at closed48
  rw [checkBlockRows_append, closed48.2, Bool.true_and, closed48.1]
  norm_num only [Nat.reduceAdd]
  have closed49 := all_parts (⟨49, by decide +kernel⟩ : Fin 65)
  change ((blocks 50).map Block.length).sum = 16384 ∧ checkBlockRows expected 868580 (blocks 50) = true at closed49
  rw [checkBlockRows_append, closed49.2, Bool.true_and, closed49.1]
  norm_num only [Nat.reduceAdd]
  have closed50 := all_parts (⟨50, by decide +kernel⟩ : Fin 65)
  change ((blocks 51).map Block.length).sum = 16384 ∧ checkBlockRows expected 884964 (blocks 51) = true at closed50
  rw [checkBlockRows_append, closed50.2, Bool.true_and, closed50.1]
  norm_num only [Nat.reduceAdd]
  have closed51 := all_parts (⟨51, by decide +kernel⟩ : Fin 65)
  change ((blocks 52).map Block.length).sum = 16384 ∧ checkBlockRows expected 901348 (blocks 52) = true at closed51
  rw [checkBlockRows_append, closed51.2, Bool.true_and, closed51.1]
  norm_num only [Nat.reduceAdd]
  have closed52 := all_parts (⟨52, by decide +kernel⟩ : Fin 65)
  change ((blocks 53).map Block.length).sum = 16384 ∧ checkBlockRows expected 917732 (blocks 53) = true at closed52
  rw [checkBlockRows_append, closed52.2, Bool.true_and, closed52.1]
  norm_num only [Nat.reduceAdd]
  have closed53 := all_parts (⟨53, by decide +kernel⟩ : Fin 65)
  change ((blocks 54).map Block.length).sum = 16384 ∧ checkBlockRows expected 934116 (blocks 54) = true at closed53
  rw [checkBlockRows_append, closed53.2, Bool.true_and, closed53.1]
  norm_num only [Nat.reduceAdd]
  have closed54 := all_parts (⟨54, by decide +kernel⟩ : Fin 65)
  change ((blocks 55).map Block.length).sum = 16384 ∧ checkBlockRows expected 950500 (blocks 55) = true at closed54
  rw [checkBlockRows_append, closed54.2, Bool.true_and, closed54.1]
  norm_num only [Nat.reduceAdd]
  have closed55 := all_parts (⟨55, by decide +kernel⟩ : Fin 65)
  change ((blocks 56).map Block.length).sum = 16384 ∧ checkBlockRows expected 966884 (blocks 56) = true at closed55
  rw [checkBlockRows_append, closed55.2, Bool.true_and, closed55.1]
  norm_num only [Nat.reduceAdd]
  have closed56 := all_parts (⟨56, by decide +kernel⟩ : Fin 65)
  change ((blocks 57).map Block.length).sum = 16384 ∧ checkBlockRows expected 983268 (blocks 57) = true at closed56
  rw [checkBlockRows_append, closed56.2, Bool.true_and, closed56.1]
  norm_num only [Nat.reduceAdd]
  have closed57 := all_parts (⟨57, by decide +kernel⟩ : Fin 65)
  change ((blocks 58).map Block.length).sum = 16384 ∧ checkBlockRows expected 999652 (blocks 58) = true at closed57
  rw [checkBlockRows_append, closed57.2, Bool.true_and, closed57.1]
  norm_num only [Nat.reduceAdd]
  have closed58 := all_parts (⟨58, by decide +kernel⟩ : Fin 65)
  change ((blocks 59).map Block.length).sum = 16384 ∧ checkBlockRows expected 1016036 (blocks 59) = true at closed58
  rw [checkBlockRows_append, closed58.2, Bool.true_and, closed58.1]
  norm_num only [Nat.reduceAdd]
  have closed59 := all_parts (⟨59, by decide +kernel⟩ : Fin 65)
  change ((blocks 60).map Block.length).sum = 16384 ∧ checkBlockRows expected 1032420 (blocks 60) = true at closed59
  rw [checkBlockRows_append, closed59.2, Bool.true_and, closed59.1]
  norm_num only [Nat.reduceAdd]
  have closed60 := all_parts (⟨60, by decide +kernel⟩ : Fin 65)
  change ((blocks 61).map Block.length).sum = 16384 ∧ checkBlockRows expected 1048804 (blocks 61) = true at closed60
  rw [checkBlockRows_append, closed60.2, Bool.true_and, closed60.1]
  norm_num only [Nat.reduceAdd]
  have closed61 := all_parts (⟨61, by decide +kernel⟩ : Fin 65)
  change ((blocks 62).map Block.length).sum = 16384 ∧ checkBlockRows expected 1065188 (blocks 62) = true at closed61
  rw [checkBlockRows_append, closed61.2, Bool.true_and, closed61.1]
  norm_num only [Nat.reduceAdd]
  have closed62 := all_parts (⟨62, by decide +kernel⟩ : Fin 65)
  change ((blocks 63).map Block.length).sum = 16384 ∧ checkBlockRows expected 1081572 (blocks 63) = true at closed62
  rw [checkBlockRows_append, closed62.2, Bool.true_and, closed62.1]
  norm_num only [Nat.reduceAdd]
  have closed63 := all_parts (⟨63, by decide +kernel⟩ : Fin 65)
  change ((blocks 64).map Block.length).sum = 16384 ∧ checkBlockRows expected 1097956 (blocks 64) = true at closed63
  rw [checkBlockRows_append, closed63.2, Bool.true_and, closed63.1]
  norm_num only [Nat.reduceAdd]
  have closed64 := all_parts (⟨64, by decide +kernel⟩ : Fin 65)
  change ((blocks 65).map Block.length).sum = 16 ∧ checkBlockRows expected 1114340 (blocks 65) = true at closed64
  exact closed64.2

/-- Every stored source output is XOR of its five original nibble keys. -/
theorem source_xor_output_get (index : Fin 1048576) :
    ((SourceCaptureParity.columns[5]?).getD ({ blocks := #[] } : Column)).get? (65780 + index.val) =
      some (index.val % 16 ^^^ (index.val / 16 % 16) ^^^ (index.val / 256 % 16) ^^^
        (index.val / 4096 % 16) ^^^ (index.val / 65536 % 16)) := by
  change getFromBlocks sourceColumn.blocks.toList (65780 + index.val) = _
  rw [source_partition, List.append_assoc]
  by_cases zero : index.val = 0
  · rw [zero, Nat.add_zero, getFromBlocks_append_left _ _ _ (by rw [front_length]; decide +kernel), front_final_zero]
    rfl
  · have lower : 1 ≤ index.val := by omega
    have position : 65780 + index.val = (frontBlocks.map Block.length).sum + (index.val - 1) := by rw [front_length]; omega
    rw [position, skip_blocks]
    have inside : index.val - 1 < (outputBlocks.map Block.length).sum := by rw [output_length]; omega
    rw [getFromBlocks_append_left _ _ _ inside]
    have checked := checkBlockRows_sound expected outputBlocks 65781 (index.val - 1) output_checked inside
    have coordinate : 65781 + (index.val - 1) - 65780 = index.val := by omega
    simpa only [expected, coordinate] using checked

/-- The complete represented-source output equals its original native value. -/
theorem source_xor_output_match (index : Fin 1048576) :
    (((SourceCaptureParity.columns[5]?).getD ({ blocks := #[] } : Column)).get? (65780 + index.val)).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.columnParityXor5.columns[5]).value index.val := by
  rw [source_xor_output_get, Option.getD_some,
    Airbender.Keccak.Split.Native.Fixed.Proofs.xor5_output_value]

end Airbender.Setup.SourceCaptureParityProofs
