import Airbender.Proofs.GKRProtocol.DecoderTail.ShiftBinop.Column0
import Airbender.Proofs.GKRProtocol.DecoderTail.ShiftBinop.Column1
import Airbender.Proofs.GKRProtocol.DecoderTail.ShiftBinop.Column2
import Airbender.Proofs.GKRProtocol.DecoderTail.ShiftBinop.Column3
import Airbender.Proofs.GKRProtocol.DecoderTail.ShiftBinop.Column4
import Airbender.Proofs.GKRProtocol.DecoderTail.ShiftBinop.Column5
import Airbender.Proofs.GKRProtocol.DecoderTail.ShiftBinop.Column6
import Airbender.Proofs.GKRProtocol.DecoderTail.ShiftBinop.Column7
import Airbender.Proofs.GKRProtocol.DecoderTail.ShiftBinop.Column8
import Airbender.Proofs.GKRProtocol.DecoderTail.ShiftBinop.Column9
import Airbender.Proofs.GKRProtocol.PackedDecoderNormalization
import Airbender.Proofs.GKRProtocol.MaterializedNative.ShiftBinopUncached

namespace Airbender.Compiler.DecoderTail.ShiftBinop.Rows
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := Airbender.Compiler.MaterializedNative.ShiftBinopUncached.native.model

def nativeRow (row : Fin 16777216) : Vector Source.BaseField 10 := (nativeSetup.imported.data.row row).map (fun n : Int => (n : Source.BaseField))

theorem real_column_length (column : Fin 10) :
    (shiftBinopSetup.realRows.columns[column.val].blocks.toList.map Setup.Block.length).sum = shiftBinopSetup.realRows.length := by
  fin_cases column <;> decide +kernel

theorem tail_column (column : Fin 10) (index : Nat) :
    nativeSetup.imported.data.columns[column.val].get? (524545 + index) =
      if index < shiftBinopSetup.realRows.length then shiftBinopSetup.realRows.columns[column.val].get? index
      else shiftBinopSetup.padding.columns[column.val].get? (index - shiftBinopSetup.realRows.length) := by
  have values : nativeSetup.imported.data.columns[column.val].get? (524545 + index) =
      Setup.getFromBlocks (shiftBinopSetup.realRows.columns[column.val].blocks.toList ++ shiftBinopSetup.padding.columns[column.val].blocks.toList) index := by
    fin_cases column
    · exact Airbender.Compiler.DecoderTail.ShiftBinop.Column0.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.ShiftBinop.Column1.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.ShiftBinop.Column2.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.ShiftBinop.Column3.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.ShiftBinop.Column4.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.ShiftBinop.Column5.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.ShiftBinop.Column6.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.ShiftBinop.Column7.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.ShiftBinop.Column8.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.ShiftBinop.Column9.decoder_tail_value index
  rw [values, getFromBlocks_append, real_column_length column]
  rfl

def dataTail (index : Nat) : Vector Nat 10 :=
  if index < shiftBinopSetup.realRows.length then shiftBinopSetup.realRows.columns.map (fun column => (column.get? index).getD 0)
  else shiftBinopSetup.padding.columns.map (fun column => (column.get? (index - shiftBinopSetup.realRows.length)).getD 0)

theorem packed_row (index : Fin (shiftBinopSetup.realRows.length + shiftBinopSetup.padding.length)) :
    shiftBinopSetup.row index = shiftBinopSetup.normalize (dataTail index.val) := by
  by_cases leading : index.val < shiftBinopSetup.realRows.length
  · simp only [PackedSetup.row, if_pos leading, dataTail,
      show shiftBinopSetup.realRows.offset = 0 from rfl, Nat.zero_add]
    rfl
  · simp only [PackedSetup.row, if_neg leading, dataTail,
      show shiftBinopSetup.padding.offset = 0 from rfl, Nat.zero_add]
    rfl

theorem raw_tail_row (index : Fin 16252671) :
    nativeRow ⟨524545 + index.val, by have := index.isLt; omega⟩ =
      (dataTail index.val).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, Setup.TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast, tail_column ⟨column, bound⟩ index.val]
  by_cases leading : index.val < shiftBinopSetup.realRows.length
  · simp only [dataTail, if_pos leading, Vector.getElem_map]
    rfl
  · simp only [dataTail, if_neg leading, Vector.getElem_map]
    rfl

theorem normalized_tail_row (index : Fin 16252671) :
    normalizeDecoderFields shiftBinopSetup (nativeRow ⟨524545 + index.val, by have := index.isLt; omega⟩) =
      (shiftBinopSetup.row ⟨index.val, by exact index.isLt⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  exact (congrArg (normalizeDecoderFields shiftBinopSetup) (raw_tail_row index)).trans
    ((normalize_decoder_fields_cast shiftBinopSetup (dataTail index.val)).trans
      (congrArg (fun values : Vector Nat 10 => values.map (fun n : Nat => (n : Source.BaseField))) (packed_row ⟨index.val, by exact index.isLt⟩)).symm)

end Airbender.Compiler.DecoderTail.ShiftBinop.Rows
