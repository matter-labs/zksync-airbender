import Airbender.Proofs.GKRProtocol.DecoderTail.JumpBranch.Rows
import Airbender.Proofs.GKRProtocol.DecoderSetupRefinement
import Airbender.Proofs.Tables.Decoder.JumpBranch

namespace Airbender.Compiler.DecoderTail.JumpBranch.Membership
open Airbender Airbender.Compiler Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := Rows.nativeSetup

column_blocks_part tagBack from Data.GKRSetup.JumpBranch.setupColumn9 start 4 stop 6

theorem tag_shape : Data.GKRSetup.JumpBranch.setupColumn9.blocks.toList = jumpBranchSetup.prefixTags.blocks.toList ++ tagBack := by rfl

theorem prefix_tag_length : (jumpBranchSetup.prefixTags.blocks.toList.map Setup.Block.length).sum = 4456448 := by decide +kernel

theorem prefix_tag (index : Fin 4456448) : Data.GKRSetup.JumpBranch.setupColumn9.get? index.val = jumpBranchSetup.prefixTags.get? index.val := by
  change Setup.getFromBlocks Data.GKRSetup.JumpBranch.setupColumn9.blocks.toList index.val = _
  rw [tag_shape]
  exact getFromBlocks_before_suffix _ tagBack index.val (by rw [prefix_tag_length]; exact index.isLt)

theorem leading_rows (row : Fin 16777216) (leading : row.val < jumpBranchSetup.offset) :
    jumpBranchSetup.tagged = true ∧ (normalizeDecoderFields jumpBranchSetup (Rows.nativeRow row))[9] =
      (Setup.signedValue ((jumpBranchSetup.prefixTags.get? row.val).getD 0) : Source.BaseField) := by
  refine ⟨by rfl, ?_⟩
  have same := prefix_tag ⟨row.val, leading⟩
  have last : (Rows.nativeRow row)[9] = (Setup.signedValue ((jumpBranchSetup.prefixTags.get? row.val).getD 0) : Source.BaseField) := by
    simp only [Rows.nativeRow, Setup.TableData.row, Vector.getElem_map, show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
    change (Setup.signedValue ((Data.GKRSetup.JumpBranch.setupColumn9.get? row.val).getD 0) : Source.BaseField) = _
    exact congrArg (fun value : Option Nat => (Setup.signedValue (value.getD 0) : Source.BaseField)) same
  simpa [normalizeDecoderFields, jumpBranchSetup, jumpBranchDecoderDataTagged] using last

theorem tail_rows (row : Fin 16777216) (outside : ¬row.val < jumpBranchSetup.offset) :
    normalizeDecoderFields jumpBranchSetup (Rows.nativeRow row) =
      (jumpBranchSetup.row ⟨row.val - jumpBranchSetup.offset, by have := row.isLt; change row.val - 4456448 < 12320768; change ¬row.val < 4456448 at outside; omega⟩).map
        (fun n => (Setup.signedValue n : Source.BaseField)) := by
  have lower : 4456448 ≤ row.val := by change ¬row.val < 4456448 at outside; omega
  let index : Fin 12320768 := ⟨row.val - 4456448, by have := row.isLt; omega⟩
  have position : (⟨4456448 + index.val, by have := index.isLt; omega⟩ : Fin 16777216) = row := by
    apply Fin.ext
    dsimp [index]
    omega
  have values := (congrArg (normalizeDecoderFields jumpBranchSetup) (congrArg Rows.nativeRow position)).symm.trans (Rows.normalized_tail_row index)
  let packedIndex : Fin (jumpBranchSetup.realRows.length + jumpBranchSetup.padding.length) := ⟨index.val, by exact index.isLt⟩
  have result : normalizeDecoderFields jumpBranchSetup (Rows.nativeRow row) = (jumpBranchSetup.row packedIndex).map (fun n : Nat => (n : Source.BaseField)) := values
  have casts : (jumpBranchSetup.row packedIndex).map (fun n : Nat => (n : Source.BaseField)) =
      (jumpBranchSetup.row packedIndex).map (fun n => (Setup.signedValue n : Source.BaseField)) := by
    apply Vector.ext
    intro column bound
    simp only [Vector.getElem_map]
    exact (Setup.signedValue_cast _).symm
  change normalizeDecoderFields jumpBranchSetup (Rows.nativeRow row) = (jumpBranchSetup.row packedIndex).map (fun n => (Setup.signedValue n : Source.BaseField))
  exact result.trans casts

theorem full_lookup (packed : Vector Source.BaseField 10) (query : Vector Source.BaseField 9)
    (normalized : normalizeDecoderFields jumpBranchSetup packed = activeQuery query)
    (member : (nativeSetup.imported.data.table "Airbender.Native.JumpBranchSlt").Contains #[] packed) : jumpBranchSetup.lookup query :=
  decoder_full_lookup_of_rows jumpBranchSetup nativeSetup.imported.data (by decide +kernel)
    leading_rows tail_rows packed query normalized _ member

theorem lookup_sound (capacity : FieldCapacity.NoWrap babyBearModulus 65536)
    (packed : Vector Source.BaseField 10) (query : Vector Source.BaseField 9) (typed : query[0].val < 65536)
    (normalized : normalizeDecoderFields jumpBranchSetup packed = activeQuery query)
    (member : (nativeSetup.imported.data.table "Airbender.Native.JumpBranchSlt").Contains #[] packed) :
    (Trace.decoderTable pooledProgram .jumpBranchSlt).Contains #[] query :=
  Trace.NativeDecoder.Proofs.JumpBranch.lookup_sound capacity query typed (full_lookup packed query normalized member)

end Airbender.Compiler.DecoderTail.JumpBranch.Membership
