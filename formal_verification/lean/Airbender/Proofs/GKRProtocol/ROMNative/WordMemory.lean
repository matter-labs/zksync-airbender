import Airbender.Proofs.GKRProtocol.ColumnSlices
import Airbender.Proofs.GKRProtocol.MaterializedNative.WordMemoryUncached
import Airbender.Proofs.Tables.ImportedROMReads

namespace Airbender.Compiler.ROMNative.WordMemory
open Airbender Airbender.Compiler
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

abbrev nativeSetup := Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model

private theorem key_column (index : Fin 1048576) :
    nativeSetup.imported.data.columns[0].get? (1 + index.val) =
      Trace.ROM.nativeWordData.columns[0].get? index.val := by
  exact column_slice_value _ _ [.dense #[0]]
    [.affine 1048576 2013265920 0, .affine 14680063 0 0] 1 1048576
    (by rfl) (by decide +kernel) (by decide +kernel) index.val index.isLt

private theorem tag_column (index : Fin 1048576) :
    nativeSetup.imported.data.columns[8].get? (1 + index.val) =
      Trace.ROM.nativeWordData.columns[8].get? index.val := by
  exact column_slice_value _ _ [.dense #[0]]
    [.affine 1048576 46 0, .affine 14680063 0 0] 1 1048576
    (by rfl) (by decide +kernel) (by decide +kernel) index.val index.isLt

private theorem output_block_bound (lane : Fin 2) :
    1 < nativeSetup.imported.data.columns[lane.val + 1].blocks.size := by
  fin_cases lane <;> decide +kernel

private theorem output_prefix (lane : Fin 2) :
    ((nativeSetup.imported.data.columns[lane.val + 1].blocks.toList.take 1).map Block.length).sum = 5 := by
  fin_cases lane <;> decide +kernel

private theorem output_tail (lane : Fin 2) :
    Setup.Proofs.zeroTail 4 Trace.ROM.nativeWordData.columns[lane.val + 1].blocks.toList = true := by
  fin_cases lane <;> decide +kernel

private theorem output_extent (lane : Fin 2) :
    (Trace.ROM.nativeWordData.columns[lane.val + 1].blocks.toList.map Block.length).sum = 1048576 := by
  fin_cases lane <;> decide +kernel

private theorem output_columns (lane : Fin 2) (index : Fin 1048576) :
    nativeSetup.imported.data.columns[lane.val + 1].get? (1 + index.val) =
      Trace.ROM.nativeWordData.columns[lane.val + 1].get? index.val := by
  by_cases leading : index.val < 4
  · have nBound := index.isLt
    generalize eq : index.val = n at *
    interval_cases n <;> fin_cases lane <;> dsimp only <;> decide +kernel
  · have lower : 4 ≤ index.val := by omega
    let full := nativeSetup.imported.data.columns[lane.val + 1]
    have blockBound : 1 < full.blocks.size := output_block_bound lane
    have fullValue := column_block_value full ⟨1, blockBound⟩
      5 (1 + index.val) (output_prefix lane) (by omega) (by
        have bound := index.isLt
        fin_cases lane <;> change 1 + index.val - 5 < 1048572 <;> omega)
    have fullShape : full.blocks[1]'blockBound = .affine 1048572 0 0 := by fin_cases lane <;> rfl
    rw [fullShape] at fullValue
    have shortValue := Setup.Proofs.zeroTail_sound 4
      Trace.ROM.nativeWordData.columns[lane.val + 1].blocks.toList
      (output_tail lane) index.val lower (by
        rw [output_extent lane]
        exact index.isLt)
    exact fullValue.trans ((constant_block_get _ _ _ (by have := index.isLt; omega)).trans shortValue.symm)

private theorem padding_columns (lane : Fin 5) (index : Fin 1048576) :
    nativeSetup.imported.data.columns[lane.val + 3].get? (1 + index.val) =
      Trace.ROM.nativeWordData.columns[lane.val + 3].get? index.val := by
  let full := nativeSetup.imported.data.columns[lane.val + 3]
  have blockBound : 0 < full.blocks.size := by fin_cases lane <;> dsimp only [full] <;> decide +kernel
  have fullValue := column_block_value full ⟨0, blockBound⟩
    0 (1 + index.val) (by rfl) (by omega) (by
      have bound := index.isLt
      fin_cases lane <;> change 1 + index.val - 0 < 1048577 <;> omega)
  have fullShape : full.blocks[0]'blockBound = .affine 1048577 0 0 := by fin_cases lane <;> rfl
  rw [fullShape] at fullValue
  have shortShape : Trace.ROM.nativeWordData.columns[lane.val + 3] = Column.mk #[.affine 1048576 0 0] := by
    fin_cases lane <;> rfl
  rw [shortShape]
  have fullZero := fullValue.trans (constant_block_get _ _ _ (by have := index.isLt; omega))
  exact fullZero.trans (by
    change some 0 = getFromBlocks [.affine 1048576 0 0] index.val
    simp [getFromBlocks, Block.get?, Block.length, index.isLt])

theorem rom_column (column : Fin 9) (index : Fin 1048576) :
    nativeSetup.imported.data.columns[column.val].get? (1 + index.val) =
      Trace.ROM.nativeWordData.columns[column.val].get? index.val := by
  fin_cases column
  · exact key_column index
  · exact output_columns 0 index
  · exact output_columns 1 index
  · exact padding_columns 0 index
  · exact padding_columns 1 index
  · exact padding_columns 2 index
  · exact padding_columns 3 index
  · exact padding_columns 4 index
  · exact tag_column index

theorem rom_row (index : Fin 1048576) :
    nativeSetup.imported.data.row ⟨1 + index.val, by have := index.isLt; change 1 + index.val < 16777216; omega⟩ =
      Trace.ROM.nativeWordData.row index := by
  apply Vector.ext
  intro column bound
  simp only [TableData.row, Vector.getElem_map]
  simp only [show nativeSetup.imported.data.offset = 0 from rfl,
    show Trace.ROM.nativeWordData.offset = 0 from rfl, Nat.zero_add]
  change signedValue ((nativeSetup.imported.data.columns[column].get? (1 + index.val)).getD 0) =
    signedValue ((Trace.ROM.nativeWordData.columns[column].get? index.val).getD 0)
  rw [rom_column ⟨column, bound⟩ index]

theorem rom_tag_region (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 8) = 34) :
    1 ≤ row.val ∧ row.val < 1048577 := by
  have value := nativeSetup.generic_cell_value row (⟨8, by decide⟩ : Fin 9)
  rw [value] at selected
  simp only [show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add] at selected
  change (((getFromBlocks [.dense #[0], .affine 1048576 34 0,
    .affine 1048576 46 0, .affine 14680063 0 0] row.val).getD 0) : Source.BaseField) = 34 at selected
  by_cases first : row.val < 1
  · have zero : row.val = 0 := by omega
    rw [zero] at selected
    exact False.elim ((by decide +kernel : (0 : Source.BaseField) ≠ 34) selected)
  · by_cases rom : row.val - 1 < 1048576
    · omega
    · by_cases decoder : row.val - 1 - 1048576 < 1048576
      · have actual : getFromBlocks [.dense #[0], .affine 1048576 34 0,
            .affine 1048576 46 0, .affine 14680063 0 0] row.val =
            (Block.affine 1048576 46 0).get? (row.val - 1 - 1048576) := by
          simp only [getFromBlocks, Block.length, show (#[0] : Array Nat).size = 1 from rfl, if_neg first, if_neg rom, if_pos decoder]
        rw [actual, constant_block_get _ _ _ decoder] at selected
        exact False.elim ((by decide +kernel : (46 : Source.BaseField) ≠ 34) selected)
      · have final : row.val - 1 - 1048576 - 1048576 < 14680063 := by
          have := row.isLt; change row.val < 16777216 at this; omega
        have actual : getFromBlocks [.dense #[0], .affine 1048576 34 0,
            .affine 1048576 46 0, .affine 14680063 0 0] row.val =
            (Block.affine 14680063 0 0).get? (row.val - 1 - 1048576 - 1048576) := by
          simp only [getFromBlocks, Block.length, show (#[0] : Array Nat).size = 1 from rfl, if_neg first, if_neg rom, if_neg decoder, if_pos final]
        rw [actual, constant_block_get _ _ _ final] at selected
        exact False.elim ((by decide +kernel : (0 : Source.BaseField) ≠ 34) selected)

theorem active_rom_refinement {query : Vector Source.BaseField 9}
    (member : (nativeSetup.imported.data.table "Airbender.Native.WordMemory").Contains #[] query)
    (tag : query[8] = 34) : (Trace.ROM.importedTable (p := babyBearModulus)).Contains #[] query := by
  obtain ⟨row, equal⟩ := member
  change query = (nativeSetup.imported.data.row row).map (fun n : Int => (n : Source.BaseField)) at equal
  have selected : nativeSetup.value row (.generic 8) = 34 := by
    rw [← tag, equal, nativeSetup.value_generic row (⟨8, by decide⟩ : Fin 9)]
    simp only [Vector.getElem_map]
  have bounds := rom_tag_region row selected
  let index : Fin 1048576 := ⟨row.val - 1, by omega⟩
  refine ⟨⟨1 + index.val, by have := index.isLt; change 1 + index.val < 1048577; omega⟩, ?_⟩
  have position : row = ⟨1 + index.val, by change 1 + index.val < 16777216; have := index.isLt; omega⟩ := Fin.ext (by dsimp [index]; omega)
  rw [position, rom_row] at equal
  exact equal.trans (by
    simp only [Trace.ROM.importedRow]
    rw [dif_neg (by change ¬ 1 + index.val < 1; omega)]
    simp only [show Trace.ROM.nativeWordZeroData.length = 1 from rfl, Nat.add_sub_cancel_left]
    rfl)

theorem native_rom_reads {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) :
    Trace.ROM.Reads (p := babyBearModulus) before (nativeSetup.imported.data.table "Airbender.Native.WordMemory") := by
  intro address lo hi bounded high member
  apply Trace.ROM.Proofs.imported_reads (p := babyBearModulus) (by decide +kernel) image address lo hi bounded high
  exact active_rom_refinement member rfl

end Airbender.Compiler.ROMNative.WordMemory
