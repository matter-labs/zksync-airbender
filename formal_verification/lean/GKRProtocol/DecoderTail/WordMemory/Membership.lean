import GKRProtocol.DecoderTail.WordMemory.Rows
import GKRProtocol.DecoderSetupRefinement
import Airbender.Proofs.Tables.Decoder.WordMemory

namespace Airbender.Compiler.DecoderTail.WordMemory.Membership
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := Rows.nativeSetup

column_blocks_part tagBack from Data.GKRSetup.WordMemory.setupColumn8 start 2 stop 4

theorem tag_shape : Data.GKRSetup.WordMemory.setupColumn8.blocks.toList = wordMemorySetup.prefixTags.blocks.toList ++ tagBack := by rfl

theorem prefix_tag_length : (wordMemorySetup.prefixTags.blocks.toList.map Setup.Block.length).sum = 1048577 := by decide +kernel

theorem prefix_tag (index : Fin 1048577) : Data.GKRSetup.WordMemory.setupColumn8.get? index.val = wordMemorySetup.prefixTags.get? index.val := by
  change Setup.getFromBlocks Data.GKRSetup.WordMemory.setupColumn8.blocks.toList index.val = _
  rw [tag_shape]
  exact getFromBlocks_before_suffix _ tagBack index.val (by rw [prefix_tag_length]; exact index.isLt)

theorem leading_rows (row : Fin 16777216) (leading : row.val < wordMemorySetup.offset) :
    wordMemorySetup.tagged = true ∧ (normalizeDecoderFields wordMemorySetup (Rows.nativeRow row))[9] =
      (Setup.signedValue ((wordMemorySetup.prefixTags.get? row.val).getD 0) : Source.BaseField) := by
  refine ⟨by rfl, ?_⟩
  have same := prefix_tag ⟨row.val, leading⟩
  have last : (Rows.nativeRow row)[8] = (Setup.signedValue ((wordMemorySetup.prefixTags.get? row.val).getD 0) : Source.BaseField) := by
    simp only [Rows.nativeRow, Setup.TableData.row, Vector.getElem_map, show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
    change (Setup.signedValue ((Data.GKRSetup.WordMemory.setupColumn8.get? row.val).getD 0) : Source.BaseField) = _
    exact congrArg (fun value : Option Nat => (Setup.signedValue (value.getD 0) : Source.BaseField)) same
  simpa [normalizeDecoderFields, wordMemorySetup, wordDecoderDataTagged] using last

theorem tail_rows (row : Fin 16777216) (outside : ¬row.val < wordMemorySetup.offset) :
    normalizeDecoderFields wordMemorySetup (Rows.nativeRow row) =
      (wordMemorySetup.row ⟨row.val - wordMemorySetup.offset, by have := row.isLt; change row.val - 1048577 < 15728639; change ¬row.val < 1048577 at outside; omega⟩).map
        (fun n => (Setup.signedValue n : Source.BaseField)) := by
  have lower : 1048577 ≤ row.val := by change ¬row.val < 1048577 at outside; omega
  let index : Fin 15728639 := ⟨row.val - 1048577, by have := row.isLt; omega⟩
  have position : (⟨1048577 + index.val, by have := index.isLt; omega⟩ : Fin 16777216) = row := by
    apply Fin.ext
    dsimp [index]
    omega
  have values := (congrArg (normalizeDecoderFields wordMemorySetup) (congrArg Rows.nativeRow position)).symm.trans (Rows.normalized_tail_row index)
  let packedIndex : Fin (wordMemorySetup.realRows.length + wordMemorySetup.padding.length) := ⟨index.val, by exact index.isLt⟩
  have result : normalizeDecoderFields wordMemorySetup (Rows.nativeRow row) = (wordMemorySetup.row packedIndex).map (fun n : Nat => (n : Source.BaseField)) := values
  have casts : (wordMemorySetup.row packedIndex).map (fun n : Nat => (n : Source.BaseField)) =
      (wordMemorySetup.row packedIndex).map (fun n => (Setup.signedValue n : Source.BaseField)) := by
    apply Vector.ext
    intro column bound
    simp only [Vector.getElem_map]
    exact (Setup.signedValue_cast _).symm
  change normalizeDecoderFields wordMemorySetup (Rows.nativeRow row) = (wordMemorySetup.row packedIndex).map (fun n => (Setup.signedValue n : Source.BaseField))
  exact result.trans casts

theorem full_lookup (packed : Vector Source.BaseField 9) (query : Vector Source.BaseField 9)
    (normalized : normalizeDecoderFields wordMemorySetup packed = activeQuery query)
    (member : (nativeSetup.imported.data.table "Airbender.Native.WordMemory").Contains #[] packed) : wordMemorySetup.lookup query :=
  decoder_full_lookup_of_rows wordMemorySetup nativeSetup.imported.data (by decide +kernel)
    leading_rows tail_rows packed query normalized _ member

theorem lookup_sound (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (packed : Vector Source.BaseField 9) (query : Vector Source.BaseField 9) (typed : query[0].val < 65536)
    (normalized : normalizeDecoderFields wordMemorySetup packed = activeQuery query)
    (member : (nativeSetup.imported.data.table "Airbender.Native.WordMemory").Contains #[] packed) :
    (Trace.decoderTable pooledProgram .wordMemory).Contains #[] query :=
  Trace.NativeDecoder.Proofs.WordMemory.lookup_sound capacity query typed (full_lookup packed query normalized member)

end Airbender.Compiler.DecoderTail.WordMemory.Membership
