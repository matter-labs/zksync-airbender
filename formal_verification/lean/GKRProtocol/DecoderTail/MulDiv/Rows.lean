import GKRProtocol.DecoderTail.MulDiv.Column0
import GKRProtocol.DecoderTail.MulDiv.Column1
import GKRProtocol.DecoderTail.MulDiv.Column2
import GKRProtocol.DecoderTail.MulDiv.Column3
import GKRProtocol.DecoderTail.MulDiv.Column4
import GKRProtocol.DecoderTail.MulDiv.Column5
import GKRProtocol.DecoderTail.MulDiv.Column6
import GKRProtocol.DecoderTail.MulDiv.Column7
import GKRProtocol.DecoderTail.MulDiv.Column8
import GKRProtocol.PackedDecoderNormalization
import GKRProtocol.MaterializedNative.MulDivUncached

namespace Airbender.Compiler.DecoderTail.MulDiv.Rows
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := Airbender.Compiler.MaterializedNative.MulDivUncached.native.model

def nativeRow (row : Fin 8388608) : Vector Source.BaseField 9 := (nativeSetup.imported.data.row row).map (fun n : Int => (n : Source.BaseField))

theorem real_column_length (column : Fin 9) :
    (mulDivSetup.realRows.columns[column.val].blocks.toList.map Setup.Block.length).sum = mulDivSetup.realRows.length := by
  fin_cases column <;> decide +kernel

theorem tail_column (column : Fin 9) (index : Nat) :
    nativeSetup.imported.data.columns[column.val].get? (270336 + index) =
      if index < mulDivSetup.realRows.length then mulDivSetup.realRows.columns[column.val].get? index
      else mulDivSetup.padding.columns[column.val].get? (index - mulDivSetup.realRows.length) := by
  have values : nativeSetup.imported.data.columns[column.val].get? (270336 + index) =
      Setup.getFromBlocks (mulDivSetup.realRows.columns[column.val].blocks.toList ++ mulDivSetup.padding.columns[column.val].blocks.toList) index := by
    fin_cases column
    · exact Airbender.Compiler.DecoderTail.MulDiv.Column0.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.MulDiv.Column1.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.MulDiv.Column2.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.MulDiv.Column3.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.MulDiv.Column4.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.MulDiv.Column5.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.MulDiv.Column6.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.MulDiv.Column7.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.MulDiv.Column8.decoder_tail_value index
  rw [values, getFromBlocks_append, real_column_length column]
  rfl

def dataTail (index : Nat) : Vector Nat 9 :=
  if index < mulDivSetup.realRows.length then mulDivSetup.realRows.columns.map (fun column => (column.get? index).getD 0)
  else mulDivSetup.padding.columns.map (fun column => (column.get? (index - mulDivSetup.realRows.length)).getD 0)

theorem packed_row (index : Fin (mulDivSetup.realRows.length + mulDivSetup.padding.length)) :
    mulDivSetup.row index = mulDivSetup.normalize (dataTail index.val) := by
  by_cases leading : index.val < mulDivSetup.realRows.length
  · simp only [PackedSetup.row, if_pos leading, dataTail,
      show mulDivSetup.realRows.offset = 0 from rfl, Nat.zero_add]
    rfl
  · simp only [PackedSetup.row, if_neg leading, dataTail,
      show mulDivSetup.padding.offset = 0 from rfl, Nat.zero_add]
    rfl

theorem raw_tail_row (index : Fin 8118272) :
    nativeRow ⟨270336 + index.val, by have := index.isLt; omega⟩ =
      (dataTail index.val).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, Setup.TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast, tail_column ⟨column, bound⟩ index.val]
  by_cases leading : index.val < mulDivSetup.realRows.length
  · simp only [dataTail, if_pos leading, Vector.getElem_map]
    rfl
  · simp only [dataTail, if_neg leading, Vector.getElem_map]
    rfl

theorem normalized_tail_row (index : Fin 8118272) :
    normalizeDecoderFields mulDivSetup (nativeRow ⟨270336 + index.val, by have := index.isLt; omega⟩) =
      (mulDivSetup.row ⟨index.val, by exact index.isLt⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  exact (congrArg (normalizeDecoderFields mulDivSetup) (raw_tail_row index)).trans
    ((normalize_decoder_fields_cast mulDivSetup (dataTail index.val)).trans
      (congrArg (fun values : Vector Nat 10 => values.map (fun n : Nat => (n : Source.BaseField))) (packed_row ⟨index.val, by exact index.isLt⟩)).symm)

end Airbender.Compiler.DecoderTail.MulDiv.Rows
