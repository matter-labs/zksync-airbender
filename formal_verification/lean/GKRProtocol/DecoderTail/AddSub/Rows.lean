import GKRProtocol.DecoderTail.AddSub.Column0
import GKRProtocol.DecoderTail.AddSub.Column1
import GKRProtocol.DecoderTail.AddSub.Column2
import GKRProtocol.DecoderTail.AddSub.Column3
import GKRProtocol.DecoderTail.AddSub.Column4
import GKRProtocol.DecoderTail.AddSub.Column5
import GKRProtocol.DecoderTail.AddSub.Column6
import GKRProtocol.DecoderTail.AddSub.Column7
import GKRProtocol.PackedDecoderNormalization
import GKRProtocol.MaterializedNative.AddSubUncached

namespace Airbender.Compiler.DecoderTail.AddSub.Rows
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := Airbender.Compiler.MaterializedNative.AddSubUncached.native.model

def nativeRow (row : Fin 16777216) : Vector Source.BaseField 8 := (nativeSetup.imported.data.row row).map (fun n : Int => (n : Source.BaseField))

theorem real_column_length (column : Fin 8) :
    (addSubSetup.realRows.columns[column.val].blocks.toList.map Setup.Block.length).sum = addSubSetup.realRows.length := by
  fin_cases column <;> decide +kernel

theorem tail_column (column : Fin 8) (index : Nat) :
    nativeSetup.imported.data.columns[column.val].get? (0 + index) =
      if index < addSubSetup.realRows.length then addSubSetup.realRows.columns[column.val].get? index
      else addSubSetup.padding.columns[column.val].get? (index - addSubSetup.realRows.length) := by
  have values : nativeSetup.imported.data.columns[column.val].get? (0 + index) =
      Setup.getFromBlocks (addSubSetup.realRows.columns[column.val].blocks.toList ++ addSubSetup.padding.columns[column.val].blocks.toList) index := by
    fin_cases column
    · exact Airbender.Compiler.DecoderTail.AddSub.Column0.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.AddSub.Column1.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.AddSub.Column2.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.AddSub.Column3.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.AddSub.Column4.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.AddSub.Column5.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.AddSub.Column6.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.AddSub.Column7.decoder_tail_value index
  rw [values, getFromBlocks_append, real_column_length column]
  rfl

def dataTail (index : Nat) : Vector Nat 8 :=
  if index < addSubSetup.realRows.length then addSubSetup.realRows.columns.map (fun column => (column.get? index).getD 0)
  else addSubSetup.padding.columns.map (fun column => (column.get? (index - addSubSetup.realRows.length)).getD 0)

theorem packed_row (index : Fin (addSubSetup.realRows.length + addSubSetup.padding.length)) :
    addSubSetup.row index = addSubSetup.normalize (dataTail index.val) := by
  by_cases leading : index.val < addSubSetup.realRows.length
  · simp only [PackedSetup.row, if_pos leading, dataTail,
      show addSubSetup.realRows.offset = 0 from rfl, Nat.zero_add]
    rfl
  · simp only [PackedSetup.row, if_neg leading, dataTail,
      show addSubSetup.padding.offset = 0 from rfl, Nat.zero_add]
    rfl

theorem raw_tail_row (index : Fin 16777216) :
    nativeRow ⟨0 + index.val, by have := index.isLt; omega⟩ =
      (dataTail index.val).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, Setup.TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  have actual := tail_column ⟨column, bound⟩ index.val
  simp only [Nat.zero_add] at actual
  rw [actual]
  by_cases leading : index.val < addSubSetup.realRows.length
  · simp only [dataTail, if_pos leading, Vector.getElem_map]
    rfl
  · simp only [dataTail, if_neg leading, Vector.getElem_map]
    rfl

theorem normalized_tail_row (index : Fin 16777216) :
    normalizeDecoderFields addSubSetup (nativeRow ⟨0 + index.val, by have := index.isLt; omega⟩) =
      (addSubSetup.row ⟨index.val, by exact index.isLt⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  exact (congrArg (normalizeDecoderFields addSubSetup) (raw_tail_row index)).trans
    ((normalize_decoder_fields_cast addSubSetup (dataTail index.val)).trans
      (congrArg (fun values : Vector Nat 10 => values.map (fun n : Nat => (n : Source.BaseField))) (packed_row ⟨index.val, by exact index.isLt⟩)).symm)

end Airbender.Compiler.DecoderTail.AddSub.Rows
