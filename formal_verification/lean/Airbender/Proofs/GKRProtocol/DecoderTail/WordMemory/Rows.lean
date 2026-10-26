import Airbender.Proofs.GKRProtocol.DecoderTail.WordMemory.Column0
import Airbender.Proofs.GKRProtocol.DecoderTail.WordMemory.Column1
import Airbender.Proofs.GKRProtocol.DecoderTail.WordMemory.Column2
import Airbender.Proofs.GKRProtocol.DecoderTail.WordMemory.Column3
import Airbender.Proofs.GKRProtocol.DecoderTail.WordMemory.Column4
import Airbender.Proofs.GKRProtocol.DecoderTail.WordMemory.Column5
import Airbender.Proofs.GKRProtocol.DecoderTail.WordMemory.Column6
import Airbender.Proofs.GKRProtocol.DecoderTail.WordMemory.Column7
import Airbender.Proofs.GKRProtocol.DecoderTail.WordMemory.Column8
import Airbender.Proofs.GKRProtocol.PackedDecoderNormalization
import Airbender.Proofs.GKRProtocol.MaterializedNative.WordMemoryUncached

namespace Airbender.Compiler.DecoderTail.WordMemory.Rows
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := Airbender.Compiler.MaterializedNative.WordMemoryUncached.native.model

def nativeRow (row : Fin 16777216) : Vector Source.BaseField 9 := (nativeSetup.imported.data.row row).map (fun n : Int => (n : Source.BaseField))

theorem real_column_length (column : Fin 9) :
    (wordMemorySetup.realRows.columns[column.val].blocks.toList.map Setup.Block.length).sum = wordMemorySetup.realRows.length := by
  fin_cases column <;> decide +kernel

theorem tail_column (column : Fin 9) (index : Nat) :
    nativeSetup.imported.data.columns[column.val].get? (1048577 + index) =
      if index < wordMemorySetup.realRows.length then wordMemorySetup.realRows.columns[column.val].get? index
      else wordMemorySetup.padding.columns[column.val].get? (index - wordMemorySetup.realRows.length) := by
  have values : nativeSetup.imported.data.columns[column.val].get? (1048577 + index) =
      Setup.getFromBlocks (wordMemorySetup.realRows.columns[column.val].blocks.toList ++ wordMemorySetup.padding.columns[column.val].blocks.toList) index := by
    fin_cases column
    · exact Airbender.Compiler.DecoderTail.WordMemory.Column0.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.WordMemory.Column1.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.WordMemory.Column2.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.WordMemory.Column3.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.WordMemory.Column4.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.WordMemory.Column5.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.WordMemory.Column6.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.WordMemory.Column7.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.WordMemory.Column8.decoder_tail_value index
  rw [values, getFromBlocks_append, real_column_length column]
  rfl

def dataTail (index : Nat) : Vector Nat 9 :=
  if index < wordMemorySetup.realRows.length then wordMemorySetup.realRows.columns.map (fun column => (column.get? index).getD 0)
  else wordMemorySetup.padding.columns.map (fun column => (column.get? (index - wordMemorySetup.realRows.length)).getD 0)

theorem packed_row (index : Fin (wordMemorySetup.realRows.length + wordMemorySetup.padding.length)) :
    wordMemorySetup.row index = wordMemorySetup.normalize (dataTail index.val) := by
  by_cases leading : index.val < wordMemorySetup.realRows.length
  · simp only [PackedSetup.row, if_pos leading, dataTail,
      show wordMemorySetup.realRows.offset = 0 from rfl, Nat.zero_add]
    rfl
  · simp only [PackedSetup.row, if_neg leading, dataTail,
      show wordMemorySetup.padding.offset = 0 from rfl, Nat.zero_add]
    rfl

theorem raw_tail_row (index : Fin 15728639) :
    nativeRow ⟨1048577 + index.val, by have := index.isLt; omega⟩ =
      (dataTail index.val).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, Setup.TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast, tail_column ⟨column, bound⟩ index.val]
  by_cases leading : index.val < wordMemorySetup.realRows.length
  · simp only [dataTail, if_pos leading, Vector.getElem_map]
    rfl
  · simp only [dataTail, if_neg leading, Vector.getElem_map]
    rfl

theorem normalized_tail_row (index : Fin 15728639) :
    normalizeDecoderFields wordMemorySetup (nativeRow ⟨1048577 + index.val, by have := index.isLt; omega⟩) =
      (wordMemorySetup.row ⟨index.val, by exact index.isLt⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  exact (congrArg (normalizeDecoderFields wordMemorySetup) (raw_tail_row index)).trans
    ((normalize_decoder_fields_cast wordMemorySetup (dataTail index.val)).trans
      (congrArg (fun values : Vector Nat 10 => values.map (fun n : Nat => (n : Source.BaseField))) (packed_row ⟨index.val, by exact index.isLt⟩)).symm)

end Airbender.Compiler.DecoderTail.WordMemory.Rows
