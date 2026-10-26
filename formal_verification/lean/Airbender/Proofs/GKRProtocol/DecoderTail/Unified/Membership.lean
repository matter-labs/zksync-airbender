import Airbender.Proofs.GKRProtocol.DecoderTail.Unified.Rows
import Airbender.Proofs.Tables.Decoder.Unified

namespace Airbender.Compiler.DecoderTail.Unified.Membership
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := Rows.nativeSetup

def tagBack : List Setup.Block := [.affine 1048576 46 0, .affine 5242495 0 0]

theorem tag_shape : Data.GKRSetup.Unified.setupColumn9.blocks.toList =
    unifiedSetup.prefixTags.blocks.toList ++ tagBack := by rfl

theorem prefix_tag_length :
    (unifiedSetup.prefixTags.blocks.toList.map Setup.Block.length).sum = 2097537 := by decide +kernel

theorem prefix_tag (index : Fin 2097537) :
    Data.GKRSetup.Unified.setupColumn9.get? index.val = unifiedSetup.prefixTags.get? index.val := by
  change Setup.getFromBlocks Data.GKRSetup.Unified.setupColumn9.blocks.toList index.val = _
  rw [tag_shape]
  exact getFromBlocks_before_suffix _ tagBack index.val (by rw [prefix_tag_length]; exact index.isLt)

theorem active_tag (query : Vector Source.BaseField 9) : (activeQuery query)[9] = 46 := by
  simp [activeQuery]

theorem full_lookup (query : Vector Source.BaseField 9)
    (member : (nativeSetup.imported.data.table "Airbender.Native.UnifiedReduced").Contains #[] (activeQuery query)) :
    unifiedSetup.lookup query := by
  obtain ⟨row, equal⟩ := member
  change activeQuery query = ROMNative.UnifiedRows.nativeRow row at equal
  refine ⟨⟨row.val, by exact row.isLt⟩, ?_⟩
  by_cases leading : row.val < 2097537
  · rw [dif_pos (show row.val < unifiedSetup.offset from leading)]
    refine ⟨by rfl, ?_⟩
    have tag := congrArg (fun vector : Vector Source.BaseField 10 => vector[9]) equal
    rw [active_tag] at tag
    simp only [ROMNative.UnifiedRows.nativeRow, Setup.TableData.row, Vector.getElem_map,
      show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add] at tag
    have same := prefix_tag ⟨row.val, leading⟩
    change Data.GKRSetup.Unified.setupColumn9.get? row.val = _ at same
    change (46 : Source.BaseField) =
      (Setup.signedValue ((Data.GKRSetup.Unified.setupColumn9.get? row.val).getD 0) : Source.BaseField) at tag
    exact tag.trans (congrArg (fun value : Option Nat =>
      (Setup.signedValue (value.getD 0) : Source.BaseField)) same)
  · rw [dif_neg (show ¬row.val < unifiedSetup.offset from leading)]
    let index : Fin 6291071 := ⟨row.val - 2097537, by have := row.isLt; change row.val < 8388608 at this; omega⟩
    have position : (⟨2097537 + index.val, by have := index.isLt; omega⟩ : Fin 8388608) = row := by
      apply Fin.ext
      dsimp [index]
      omega
    have same := (congrArg ROMNative.UnifiedRows.nativeRow position).symm.trans (Rows.decoder_tail_row index)
    let packedIndex : Fin (unifiedSetup.realRows.length + unifiedSetup.padding.length) := ⟨index.val, by exact index.isLt⟩
    have result : activeQuery query = (unifiedSetup.row packedIndex).map (fun n : Nat => (n : Source.BaseField)) := equal.trans same
    have casts : (unifiedSetup.row packedIndex).map (fun n : Nat => (n : Source.BaseField)) =
        (unifiedSetup.row packedIndex).map (fun n => (Setup.signedValue n : Source.BaseField)) := by
      apply Vector.ext
      intro column bound
      simp only [Vector.getElem_map]
      exact (Setup.signedValue_cast _).symm
    change activeQuery query = (unifiedSetup.row packedIndex).map (fun n => (Setup.signedValue n : Source.BaseField))
    exact result.trans casts

theorem lookup_sound (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (query : Vector Source.BaseField 9) (typed : query[0].val < 65536)
    (member : (nativeSetup.imported.data.table "Airbender.Native.UnifiedReduced").Contains #[] (activeQuery query)) :
    (Trace.decoderTable unifiedProgram .machine).Contains #[] query :=
  Trace.NativeDecoder.Proofs.Unified.lookup_sound capacity query typed (full_lookup query member)

end Airbender.Compiler.DecoderTail.Unified.Membership
