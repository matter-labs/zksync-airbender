import GKRProtocol.DecoderTail.SubwordMemory.Rows
import GKRProtocol.DecoderSetupRefinement
import Airbender.Proofs.Tables.Decoder.Subword

namespace Airbender.Compiler.DecoderTail.SubwordMemory.Membership
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := Rows.nativeSetup

column_blocks_part tagBack from Data.GKRSetup.SubwordMemory.setupColumn8 start 7 stop 9

theorem tag_shape : Data.GKRSetup.SubwordMemory.setupColumn8.blocks.toList = subwordSetup.prefixTags.blocks.toList ++ tagBack := by rfl

theorem prefix_tag_length : (subwordSetup.prefixTags.blocks.toList.map Setup.Block.length).sum = 13238273 := by decide +kernel

theorem prefix_tag (index : Fin 13238273) : Data.GKRSetup.SubwordMemory.setupColumn8.get? index.val = subwordSetup.prefixTags.get? index.val := by
  change Setup.getFromBlocks Data.GKRSetup.SubwordMemory.setupColumn8.blocks.toList index.val = _
  rw [tag_shape]
  exact getFromBlocks_before_suffix _ tagBack index.val (by rw [prefix_tag_length]; exact index.isLt)

theorem leading_rows (row : Fin 16777216) (leading : row.val < subwordSetup.offset) :
    subwordSetup.tagged = true ∧ (normalizeDecoderFields subwordSetup (Rows.nativeRow row))[9] =
      (Setup.signedValue ((subwordSetup.prefixTags.get? row.val).getD 0) : Source.BaseField) := by
  refine ⟨by rfl, ?_⟩
  have same := prefix_tag ⟨row.val, leading⟩
  have last : (Rows.nativeRow row)[8] = (Setup.signedValue ((subwordSetup.prefixTags.get? row.val).getD 0) : Source.BaseField) := by
    simp only [Rows.nativeRow, Setup.TableData.row, Vector.getElem_map, show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
    change (Setup.signedValue ((Data.GKRSetup.SubwordMemory.setupColumn8.get? row.val).getD 0) : Source.BaseField) = _
    exact congrArg (fun value : Option Nat => (Setup.signedValue (value.getD 0) : Source.BaseField)) same
  simpa [normalizeDecoderFields, subwordSetup, subwordDecoderDataTagged] using last

theorem tail_rows (row : Fin 16777216) (outside : ¬row.val < subwordSetup.offset) :
    normalizeDecoderFields subwordSetup (Rows.nativeRow row) =
      (subwordSetup.row ⟨row.val - subwordSetup.offset, by have := row.isLt; change row.val - 13238273 < 3538943; change ¬row.val < 13238273 at outside; omega⟩).map
        (fun n => (Setup.signedValue n : Source.BaseField)) := by
  have lower : 13238273 ≤ row.val := by change ¬row.val < 13238273 at outside; omega
  let index : Fin 3538943 := ⟨row.val - 13238273, by have := row.isLt; omega⟩
  have position : (⟨13238273 + index.val, by have := index.isLt; omega⟩ : Fin 16777216) = row := by
    apply Fin.ext
    dsimp [index]
    omega
  have values := (congrArg (normalizeDecoderFields subwordSetup) (congrArg Rows.nativeRow position)).symm.trans (Rows.normalized_tail_row index)
  let packedIndex : Fin (subwordSetup.realRows.length + subwordSetup.padding.length) := ⟨index.val, by exact index.isLt⟩
  have result : normalizeDecoderFields subwordSetup (Rows.nativeRow row) = (subwordSetup.row packedIndex).map (fun n : Nat => (n : Source.BaseField)) := values
  have casts : (subwordSetup.row packedIndex).map (fun n : Nat => (n : Source.BaseField)) =
      (subwordSetup.row packedIndex).map (fun n => (Setup.signedValue n : Source.BaseField)) := by
    apply Vector.ext
    intro column bound
    simp only [Vector.getElem_map]
    exact (Setup.signedValue_cast _).symm
  change normalizeDecoderFields subwordSetup (Rows.nativeRow row) = (subwordSetup.row packedIndex).map (fun n => (Setup.signedValue n : Source.BaseField))
  exact result.trans casts

theorem full_lookup (packed : Vector Source.BaseField 9) (query : Vector Source.BaseField 9)
    (normalized : normalizeDecoderFields subwordSetup packed = activeQuery query)
    (member : (nativeSetup.imported.data.table "Airbender.Native.SubwordMemory").Contains #[] packed) : subwordSetup.lookup query :=
  decoder_full_lookup_of_rows subwordSetup nativeSetup.imported.data (by decide +kernel)
    leading_rows tail_rows packed query normalized _ member

theorem lookup_sound (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (packed : Vector Source.BaseField 9) (query : Vector Source.BaseField 9) (typed : query[0].val < 65536)
    (normalized : normalizeDecoderFields subwordSetup packed = activeQuery query)
    (member : (nativeSetup.imported.data.table "Airbender.Native.SubwordMemory").Contains #[] packed) :
    (Trace.decoderTable pooledProgram .subwordMemory).Contains #[] query :=
  Trace.NativeDecoder.Proofs.Subword.lookup_sound capacity query typed (full_lookup packed query normalized member)

end Airbender.Compiler.DecoderTail.SubwordMemory.Membership
