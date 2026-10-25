import GKRProtocol.DecoderTail.SubwordMemory.Column0
import GKRProtocol.DecoderTail.SubwordMemory.Column1
import GKRProtocol.DecoderTail.SubwordMemory.Column2
import GKRProtocol.DecoderTail.SubwordMemory.Column3
import GKRProtocol.DecoderTail.SubwordMemory.Column4
import GKRProtocol.DecoderTail.SubwordMemory.Column5
import GKRProtocol.DecoderTail.SubwordMemory.Column6
import GKRProtocol.DecoderTail.SubwordMemory.Column7
import GKRProtocol.DecoderTail.SubwordMemory.Column8
import GKRProtocol.PackedDecoderNormalization
import GKRProtocol.MaterializedNative.SubwordMemoryUncached

namespace Airbender.Compiler.DecoderTail.SubwordMemory.Rows
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model

def nativeRow (row : Fin 16777216) : Vector Source.BaseField 9 := (nativeSetup.imported.data.row row).map (fun n : Int => (n : Source.BaseField))

theorem real_column_length (column : Fin 9) :
    (subwordSetup.realRows.columns[column.val].blocks.toList.map Setup.Block.length).sum = subwordSetup.realRows.length := by
  fin_cases column <;> decide +kernel

theorem tail_column (column : Fin 9) (index : Nat) :
    nativeSetup.imported.data.columns[column.val].get? (13238273 + index) =
      if index < subwordSetup.realRows.length then subwordSetup.realRows.columns[column.val].get? index
      else subwordSetup.padding.columns[column.val].get? (index - subwordSetup.realRows.length) := by
  have values : nativeSetup.imported.data.columns[column.val].get? (13238273 + index) =
      Setup.getFromBlocks (subwordSetup.realRows.columns[column.val].blocks.toList ++ subwordSetup.padding.columns[column.val].blocks.toList) index := by
    fin_cases column
    · exact Airbender.Compiler.DecoderTail.SubwordMemory.Column0.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.SubwordMemory.Column1.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.SubwordMemory.Column2.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.SubwordMemory.Column3.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.SubwordMemory.Column4.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.SubwordMemory.Column5.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.SubwordMemory.Column6.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.SubwordMemory.Column7.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.SubwordMemory.Column8.decoder_tail_value index
  rw [values, getFromBlocks_append, real_column_length column]
  rfl

def dataTail (index : Nat) : Vector Nat 9 :=
  if index < subwordSetup.realRows.length then subwordSetup.realRows.columns.map (fun column => (column.get? index).getD 0)
  else subwordSetup.padding.columns.map (fun column => (column.get? (index - subwordSetup.realRows.length)).getD 0)

theorem packed_row (index : Fin (subwordSetup.realRows.length + subwordSetup.padding.length)) :
    subwordSetup.row index = subwordSetup.normalize (dataTail index.val) := by
  by_cases leading : index.val < subwordSetup.realRows.length
  · simp only [PackedSetup.row, if_pos leading, dataTail,
      show subwordSetup.realRows.offset = 0 from rfl, Nat.zero_add]
    rfl
  · simp only [PackedSetup.row, if_neg leading, dataTail,
      show subwordSetup.padding.offset = 0 from rfl, Nat.zero_add]
    rfl

theorem raw_tail_row (index : Fin 3538943) :
    nativeRow ⟨13238273 + index.val, by have := index.isLt; omega⟩ =
      (dataTail index.val).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, Setup.TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast, tail_column ⟨column, bound⟩ index.val]
  by_cases leading : index.val < subwordSetup.realRows.length
  · simp only [dataTail, if_pos leading, Vector.getElem_map]
    rfl
  · simp only [dataTail, if_neg leading, Vector.getElem_map]
    rfl

theorem normalized_tail_row (index : Fin 3538943) :
    normalizeDecoderFields subwordSetup (nativeRow ⟨13238273 + index.val, by have := index.isLt; omega⟩) =
      (subwordSetup.row ⟨index.val, by exact index.isLt⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  exact (congrArg (normalizeDecoderFields subwordSetup) (raw_tail_row index)).trans
    ((normalize_decoder_fields_cast subwordSetup (dataTail index.val)).trans
      (congrArg (fun values : Vector Nat 10 => values.map (fun n : Nat => (n : Source.BaseField))) (packed_row ⟨index.val, by exact index.isLt⟩)).symm)

end Airbender.Compiler.DecoderTail.SubwordMemory.Rows
