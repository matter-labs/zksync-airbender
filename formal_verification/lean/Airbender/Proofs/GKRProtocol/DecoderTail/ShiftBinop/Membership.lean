import Airbender.Proofs.GKRProtocol.DecoderTail.ShiftBinop.Rows
import Airbender.Proofs.GKRProtocol.DecoderSetupRefinement
import Airbender.Proofs.Tables.Decoder.ShiftBinop

namespace Airbender.Compiler.DecoderTail.ShiftBinop.Membership
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := Rows.nativeSetup

column_blocks_part tagBack from Data.GKRSetup.ShiftBinop.setupColumn9 start 7 stop 9

theorem tag_shape : Data.GKRSetup.ShiftBinop.setupColumn9.blocks.toList = shiftBinopSetup.prefixTags.blocks.toList ++ tagBack := by rfl

theorem prefix_tag_length : (shiftBinopSetup.prefixTags.blocks.toList.map Setup.Block.length).sum = 524545 := by decide +kernel

theorem prefix_tag (index : Fin 524545) : Data.GKRSetup.ShiftBinop.setupColumn9.get? index.val = shiftBinopSetup.prefixTags.get? index.val := by
  change Setup.getFromBlocks Data.GKRSetup.ShiftBinop.setupColumn9.blocks.toList index.val = _
  rw [tag_shape]
  exact getFromBlocks_before_suffix _ tagBack index.val (by rw [prefix_tag_length]; exact index.isLt)

theorem leading_rows (row : Fin 16777216) (leading : row.val < shiftBinopSetup.offset) :
    shiftBinopSetup.tagged = true ∧ (normalizeDecoderFields shiftBinopSetup (Rows.nativeRow row))[9] =
      (Setup.signedValue ((shiftBinopSetup.prefixTags.get? row.val).getD 0) : Source.BaseField) := by
  refine ⟨by rfl, ?_⟩
  have same := prefix_tag ⟨row.val, leading⟩
  have last : (Rows.nativeRow row)[9] = (Setup.signedValue ((shiftBinopSetup.prefixTags.get? row.val).getD 0) : Source.BaseField) := by
    simp only [Rows.nativeRow, Setup.TableData.row, Vector.getElem_map, show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
    change (Setup.signedValue ((Data.GKRSetup.ShiftBinop.setupColumn9.get? row.val).getD 0) : Source.BaseField) = _
    exact congrArg (fun value : Option Nat => (Setup.signedValue (value.getD 0) : Source.BaseField)) same
  simpa [normalizeDecoderFields, shiftBinopSetup, shiftDecoderDataTagged] using last

theorem tail_rows (row : Fin 16777216) (outside : ¬row.val < shiftBinopSetup.offset) :
    normalizeDecoderFields shiftBinopSetup (Rows.nativeRow row) =
      (shiftBinopSetup.row ⟨row.val - shiftBinopSetup.offset, by have := row.isLt; change row.val - 524545 < 16252671; change ¬row.val < 524545 at outside; omega⟩).map
        (fun n => (Setup.signedValue n : Source.BaseField)) := by
  have lower : 524545 ≤ row.val := by change ¬row.val < 524545 at outside; omega
  let index : Fin 16252671 := ⟨row.val - 524545, by have := row.isLt; omega⟩
  have position : (⟨524545 + index.val, by have := index.isLt; omega⟩ : Fin 16777216) = row := by
    apply Fin.ext
    dsimp [index]
    omega
  have values := (congrArg (normalizeDecoderFields shiftBinopSetup) (congrArg Rows.nativeRow position)).symm.trans (Rows.normalized_tail_row index)
  let packedIndex : Fin (shiftBinopSetup.realRows.length + shiftBinopSetup.padding.length) := ⟨index.val, by exact index.isLt⟩
  have result : normalizeDecoderFields shiftBinopSetup (Rows.nativeRow row) = (shiftBinopSetup.row packedIndex).map (fun n : Nat => (n : Source.BaseField)) := values
  have casts : (shiftBinopSetup.row packedIndex).map (fun n : Nat => (n : Source.BaseField)) =
      (shiftBinopSetup.row packedIndex).map (fun n => (Setup.signedValue n : Source.BaseField)) := by
    apply Vector.ext
    intro column bound
    simp only [Vector.getElem_map]
    exact (Setup.signedValue_cast _).symm
  change normalizeDecoderFields shiftBinopSetup (Rows.nativeRow row) = (shiftBinopSetup.row packedIndex).map (fun n => (Setup.signedValue n : Source.BaseField))
  exact result.trans casts

theorem full_lookup (packed : Vector Source.BaseField 10) (query : Vector Source.BaseField 9)
    (normalized : normalizeDecoderFields shiftBinopSetup packed = activeQuery query)
    (member : (nativeSetup.imported.data.table "Airbender.Native.ShiftBinop").Contains #[] packed) : shiftBinopSetup.lookup query :=
  decoder_full_lookup_of_rows shiftBinopSetup nativeSetup.imported.data (by decide +kernel)
    leading_rows tail_rows packed query normalized _ member

theorem lookup_sound (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (packed : Vector Source.BaseField 10) (query : Vector Source.BaseField 9) (typed : query[0].val < 65536)
    (normalized : normalizeDecoderFields shiftBinopSetup packed = activeQuery query)
    (member : (nativeSetup.imported.data.table "Airbender.Native.ShiftBinop").Contains #[] packed) :
    (Trace.decoderTable pooledProgram .shiftBinop).Contains #[] query :=
  Trace.NativeDecoder.Proofs.ShiftBinop.lookup_sound capacity query typed (full_lookup packed query normalized member)

end Airbender.Compiler.DecoderTail.ShiftBinop.Membership
