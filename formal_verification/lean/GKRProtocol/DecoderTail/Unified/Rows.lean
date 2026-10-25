import GKRProtocol.DecoderTail.Unified.Column0
import GKRProtocol.DecoderTail.Unified.Column1
import GKRProtocol.DecoderTail.Unified.Column2
import GKRProtocol.DecoderTail.Unified.Column3
import GKRProtocol.DecoderTail.Unified.Column4
import GKRProtocol.DecoderTail.Unified.Column5
import GKRProtocol.DecoderTail.Unified.Column6
import GKRProtocol.DecoderTail.Unified.Column7
import GKRProtocol.DecoderTail.Unified.Column8
import GKRProtocol.DecoderTail.Unified.Column9
import GKRProtocol.PackedDecoderNormalization
import GKRProtocol.ROMNative.UnifiedRows

namespace Airbender.Compiler.DecoderTail.Unified.Rows
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := ROMNative.UnifiedRows.nativeSetup

theorem normalize_identity (values : Vector Nat 10) : unifiedSetup.normalize values = values := by
  apply Vector.ext
  intro column bound
  simp only [PackedSetup.normalize, Vector.getElem_ofFn]
  interval_cases column <;> simp [unifiedSetup, unifiedDecoderDataColumnsMask, unifiedDecoderDataTagged]

theorem normalize_fields_identity (packed : Vector Source.BaseField 10) :
    normalizeDecoderFields unifiedSetup packed = packed := by
  apply Vector.ext
  intro column bound
  simp only [normalizeDecoderFields, Vector.getElem_ofFn]
  interval_cases column <;> simp [unifiedSetup, unifiedDecoderDataColumnsMask, unifiedDecoderDataTagged]

theorem real_column_length (column : Fin 10) :
    (unifiedSetup.realRows.columns[column.val].blocks.toList.map Setup.Block.length).sum =
      unifiedSetup.realRows.length := by
  fin_cases column <;> decide +kernel

theorem tail_column (column : Fin 10) (index : Nat) :
    nativeSetup.imported.data.columns[column.val].get? (2097537 + index) =
      if index < unifiedSetup.realRows.length then unifiedSetup.realRows.columns[column.val].get? index
      else unifiedSetup.padding.columns[column.val].get? (index - unifiedSetup.realRows.length) := by
  have values : nativeSetup.imported.data.columns[column.val].get? (2097537 + index) =
      Setup.getFromBlocks (unifiedSetup.realRows.columns[column.val].blocks.toList ++
        unifiedSetup.padding.columns[column.val].blocks.toList) index := by
    fin_cases column
    · exact Airbender.Compiler.DecoderTail.Unified.Column0.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.Unified.Column1.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.Unified.Column2.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.Unified.Column3.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.Unified.Column4.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.Unified.Column5.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.Unified.Column6.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.Unified.Column7.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.Unified.Column8.decoder_tail_value index
    · exact Airbender.Compiler.DecoderTail.Unified.Column9.decoder_tail_value index
  rw [values, getFromBlocks_append, real_column_length column]
  rfl

def dataTail (index : Nat) : Vector Nat 10 :=
  if index < unifiedSetup.realRows.length then
    unifiedSetup.realRows.columns.map (fun column => (column.get? index).getD 0)
  else unifiedSetup.padding.columns.map
    (fun column => (column.get? (index - unifiedSetup.realRows.length)).getD 0)

theorem packed_row (index : Fin (unifiedSetup.realRows.length + unifiedSetup.padding.length)) :
    unifiedSetup.row index = dataTail index.val := by
  by_cases leading : index.val < unifiedSetup.realRows.length
  · simp only [PackedSetup.row, if_pos leading, normalize_identity, dataTail,
      show unifiedSetup.realRows.offset = 0 from rfl, Nat.zero_add]
    rfl
  · simp only [PackedSetup.row, if_neg leading, normalize_identity, dataTail,
      show unifiedSetup.padding.offset = 0 from rfl, Nat.zero_add]
    rfl

theorem decoder_tail_row (index : Fin 6291071) :
    ROMNative.UnifiedRows.nativeRow ⟨2097537 + index.val, by have := index.isLt; omega⟩ =
      (unifiedSetup.row ⟨index.val, by exact index.isLt⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  rw [packed_row]
  apply Vector.ext
  intro column bound
  simp only [ROMNative.UnifiedRows.nativeRow, Setup.TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast, tail_column ⟨column, bound⟩ index.val]
  by_cases leading : index.val < unifiedSetup.realRows.length
  · simp only [dataTail, if_pos leading, Vector.getElem_map]
    rfl
  · simp only [dataTail, if_neg leading, Vector.getElem_map]
    rfl

end Airbender.Compiler.DecoderTail.Unified.Rows
