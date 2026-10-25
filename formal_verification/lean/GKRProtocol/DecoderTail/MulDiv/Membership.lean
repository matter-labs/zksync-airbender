import GKRProtocol.DecoderTail.MulDiv.Rows
import GKRProtocol.DecoderSetupRefinement
import Airbender.Proofs.Tables.Decoder.MulDiv

namespace Airbender.Compiler.DecoderTail.MulDiv.Membership
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := Rows.nativeSetup

column_blocks_part tagBack from Data.GKRSetup.MulDiv.setupColumn8 start 4 stop 6

theorem tag_shape : Data.GKRSetup.MulDiv.setupColumn8.blocks.toList = mulDivSetup.prefixTags.blocks.toList ++ tagBack := by rfl

theorem prefix_tag_length : (mulDivSetup.prefixTags.blocks.toList.map Setup.Block.length).sum = 270336 := by decide +kernel

theorem prefix_tag (index : Fin 270336) : Data.GKRSetup.MulDiv.setupColumn8.get? index.val = mulDivSetup.prefixTags.get? index.val := by
  change Setup.getFromBlocks Data.GKRSetup.MulDiv.setupColumn8.blocks.toList index.val = _
  rw [tag_shape]
  exact getFromBlocks_before_suffix _ tagBack index.val (by rw [prefix_tag_length]; exact index.isLt)

theorem leading_rows (row : Fin 8388608) (leading : row.val < mulDivSetup.offset) :
    mulDivSetup.tagged = true ∧ (normalizeDecoderFields mulDivSetup (Rows.nativeRow row))[9] =
      (Setup.signedValue ((mulDivSetup.prefixTags.get? row.val).getD 0) : Source.BaseField) := by
  refine ⟨by rfl, ?_⟩
  have same := prefix_tag ⟨row.val, leading⟩
  have last : (Rows.nativeRow row)[8] = (Setup.signedValue ((mulDivSetup.prefixTags.get? row.val).getD 0) : Source.BaseField) := by
    simp only [Rows.nativeRow, Setup.TableData.row, Vector.getElem_map, show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
    change (Setup.signedValue ((Data.GKRSetup.MulDiv.setupColumn8.get? row.val).getD 0) : Source.BaseField) = _
    exact congrArg (fun value : Option Nat => (Setup.signedValue (value.getD 0) : Source.BaseField)) same
  simpa [normalizeDecoderFields, mulDivSetup, mulDivDecoderDataTagged] using last

theorem tail_rows (row : Fin 8388608) (outside : ¬row.val < mulDivSetup.offset) :
    normalizeDecoderFields mulDivSetup (Rows.nativeRow row) =
      (mulDivSetup.row ⟨row.val - mulDivSetup.offset, by have := row.isLt; change row.val - 270336 < 8118272; change ¬row.val < 270336 at outside; omega⟩).map
        (fun n => (Setup.signedValue n : Source.BaseField)) := by
  have lower : 270336 ≤ row.val := by change ¬row.val < 270336 at outside; omega
  let index : Fin 8118272 := ⟨row.val - 270336, by have := row.isLt; omega⟩
  have position : (⟨270336 + index.val, by have := index.isLt; omega⟩ : Fin 8388608) = row := by
    apply Fin.ext
    dsimp [index]
    omega
  have values := (congrArg (normalizeDecoderFields mulDivSetup) (congrArg Rows.nativeRow position)).symm.trans (Rows.normalized_tail_row index)
  let packedIndex : Fin (mulDivSetup.realRows.length + mulDivSetup.padding.length) := ⟨index.val, by exact index.isLt⟩
  have result : normalizeDecoderFields mulDivSetup (Rows.nativeRow row) = (mulDivSetup.row packedIndex).map (fun n : Nat => (n : Source.BaseField)) := values
  have casts : (mulDivSetup.row packedIndex).map (fun n : Nat => (n : Source.BaseField)) =
      (mulDivSetup.row packedIndex).map (fun n => (Setup.signedValue n : Source.BaseField)) := by
    apply Vector.ext
    intro column bound
    simp only [Vector.getElem_map]
    exact (Setup.signedValue_cast _).symm
  change normalizeDecoderFields mulDivSetup (Rows.nativeRow row) = (mulDivSetup.row packedIndex).map (fun n => (Setup.signedValue n : Source.BaseField))
  exact result.trans casts

theorem full_lookup (packed : Vector Source.BaseField 9) (query : Vector Source.BaseField 9)
    (normalized : normalizeDecoderFields mulDivSetup packed = activeQuery query)
    (member : (nativeSetup.imported.data.table "Airbender.Native.MulDiv").Contains #[] packed) : mulDivSetup.lookup query :=
  decoder_full_lookup_of_rows mulDivSetup nativeSetup.imported.data (by decide +kernel)
    leading_rows tail_rows packed query normalized _ member

theorem lookup_sound (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (packed : Vector Source.BaseField 9) (query : Vector Source.BaseField 9) (typed : query[0].val < 65536)
    (normalized : normalizeDecoderFields mulDivSetup packed = activeQuery query)
    (member : (nativeSetup.imported.data.table "Airbender.Native.MulDiv").Contains #[] packed) :
    (Trace.decoderTable pooledProgram .mulDiv).Contains #[] query :=
  Trace.NativeDecoder.Proofs.MulDiv.lookup_sound capacity query typed (full_lookup packed query normalized member)

end Airbender.Compiler.DecoderTail.MulDiv.Membership
