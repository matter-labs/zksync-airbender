import GKRProtocol.ROMNative.UnifiedRows
import GKRProtocol.ROMNative.UnifiedTag

namespace Airbender.Compiler.ROMNative.UnifiedBoundary
open Airbender Airbender.Compiler Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := UnifiedRows.nativeSetup

column_blocks_part paddingFront0 from Data.GKRSetup.Unified.setupColumn0 start 19 stop 21

theorem paddingShape0 : UnifiedAllPrefix.Column0.suffix = paddingFront0 ++ [Block.affine 5242495 0 0] := by rfl

theorem paddingFrontLength0 : (paddingFront0.map Block.length).sum = 1048576 := by decide +kernel

theorem paddingValue0 (row : Fin 8388608) (lower : 3146113 ≤ row.val) : Data.GKRSetup.Unified.setupColumn0.get? row.val = some 0 := by
  change Setup.getFromBlocks Data.GKRSetup.Unified.setupColumn0.blocks.toList row.val = _
  rw [UnifiedAllPrefix.Column0.sourceShape, getFromBlocks_append, UnifiedAllPrefix.Column0.originalLength, if_neg (by omega), paddingShape0, getFromBlocks_append, paddingFrontLength0, if_neg (by omega)]
  rw [Setup.getFromBlocks, if_pos (by have := row.isLt; change row.val - 2097537 - 1048576 < 5242495; omega)]
  exact constant_block_get _ _ _ (by have := row.isLt; omega)

column_blocks_part paddingFront1 from Data.GKRSetup.Unified.setupColumn1 start 34 stop 36

theorem paddingShape1 : UnifiedPrefixNative.Column1.suffix = paddingFront1 ++ [Block.affine 5242495 0 0] := by rfl

theorem paddingFrontLength1 : (paddingFront1.map Block.length).sum = 1048575 := by decide +kernel

theorem paddingValue1 (row : Fin 8388608) (lower : 3146113 ≤ row.val) : Data.GKRSetup.Unified.setupColumn1.get? row.val = some 0 := by
  change Setup.getFromBlocks Data.GKRSetup.Unified.setupColumn1.blocks.toList row.val = _
  rw [UnifiedPrefixNative.Column1.sourceShape, getFromBlocks_append, UnifiedPrefixNative.Column1.originalLength, if_neg (by omega), paddingShape1, getFromBlocks_append, paddingFrontLength1, if_neg (by omega)]
  rw [Setup.getFromBlocks, if_pos (by have := row.isLt; change row.val - 2097538 - 1048575 < 5242495; omega)]
  exact constant_block_get _ _ _ (by have := row.isLt; omega)

column_blocks_part paddingFront2 from Data.GKRSetup.Unified.setupColumn2 start 2712 stop 2714

theorem paddingShape2 : UnifiedAllPrefix.Column2.suffix = paddingFront2 ++ [Block.affine 5242495 0 0] := by rfl

theorem paddingFrontLength2 : (paddingFront2.map Block.length).sum = 1048576 := by decide +kernel

theorem paddingValue2 (row : Fin 8388608) (lower : 3146113 ≤ row.val) : Data.GKRSetup.Unified.setupColumn2.get? row.val = some 0 := by
  change Setup.getFromBlocks Data.GKRSetup.Unified.setupColumn2.blocks.toList row.val = _
  rw [UnifiedAllPrefix.Column2.sourceShape, getFromBlocks_append, UnifiedAllPrefix.Column2.originalLength, if_neg (by omega), paddingShape2, getFromBlocks_append, paddingFrontLength2, if_neg (by omega)]
  rw [Setup.getFromBlocks, if_pos (by have := row.isLt; change row.val - 2097537 - 1048576 < 5242495; omega)]
  exact constant_block_get _ _ _ (by have := row.isLt; omega)

column_blocks_part paddingFront3 from Data.GKRSetup.Unified.setupColumn3 start 3 stop 5

theorem paddingShape3 : UnifiedAllPrefix.Column3.suffix = paddingFront3 ++ [Block.affine 5242495 0 0] := by rfl

theorem paddingFrontLength3 : (paddingFront3.map Block.length).sum = 1048573 := by decide +kernel

theorem paddingValue3 (row : Fin 8388608) (lower : 3146113 ≤ row.val) : Data.GKRSetup.Unified.setupColumn3.get? row.val = some 0 := by
  change Setup.getFromBlocks Data.GKRSetup.Unified.setupColumn3.blocks.toList row.val = _
  rw [UnifiedAllPrefix.Column3.sourceShape, getFromBlocks_append, UnifiedAllPrefix.Column3.originalLength, if_neg (by omega), paddingShape3, getFromBlocks_append, paddingFrontLength3, if_neg (by omega)]
  rw [Setup.getFromBlocks, if_pos (by have := row.isLt; change row.val - 2097540 - 1048573 < 5242495; omega)]
  exact constant_block_get _ _ _ (by have := row.isLt; omega)

column_blocks_part paddingFront4 from Data.GKRSetup.Unified.setupColumn4 start 25570 stop 25572

theorem paddingShape4 : UnifiedAllPrefix.Column4.suffix = paddingFront4 ++ [Block.affine 5242495 0 0] := by rfl

theorem paddingFrontLength4 : (paddingFront4.map Block.length).sum = 1048575 := by decide +kernel

theorem paddingValue4 (row : Fin 8388608) (lower : 3146113 ≤ row.val) : Data.GKRSetup.Unified.setupColumn4.get? row.val = some 0 := by
  change Setup.getFromBlocks Data.GKRSetup.Unified.setupColumn4.blocks.toList row.val = _
  rw [UnifiedAllPrefix.Column4.sourceShape, getFromBlocks_append, UnifiedAllPrefix.Column4.originalLength, if_neg (by omega), paddingShape4, getFromBlocks_append, paddingFrontLength4, if_neg (by omega)]
  rw [Setup.getFromBlocks, if_pos (by have := row.isLt; change row.val - 2097538 - 1048575 < 5242495; omega)]
  exact constant_block_get _ _ _ (by have := row.isLt; omega)

column_blocks_part paddingFront5 from Data.GKRSetup.Unified.setupColumn5 start 26491 stop 26493

theorem paddingShape5 : UnifiedAllPrefix.Column5.suffix = paddingFront5 ++ [Block.affine 5242495 0 0] := by rfl

theorem paddingFrontLength5 : (paddingFront5.map Block.length).sum = 1048575 := by decide +kernel

theorem paddingValue5 (row : Fin 8388608) (lower : 3146113 ≤ row.val) : Data.GKRSetup.Unified.setupColumn5.get? row.val = some 0 := by
  change Setup.getFromBlocks Data.GKRSetup.Unified.setupColumn5.blocks.toList row.val = _
  rw [UnifiedAllPrefix.Column5.sourceShape, getFromBlocks_append, UnifiedAllPrefix.Column5.originalLength, if_neg (by omega), paddingShape5, getFromBlocks_append, paddingFrontLength5, if_neg (by omega)]
  rw [Setup.getFromBlocks, if_pos (by have := row.isLt; change row.val - 2097538 - 1048575 < 5242495; omega)]
  exact constant_block_get _ _ _ (by have := row.isLt; omega)

column_blocks_part paddingFront6 from Data.GKRSetup.Unified.setupColumn6 start 24287 stop 24288

theorem paddingShape6 : UnifiedAllPrefix.Column6.suffix = paddingFront6 ++ [Block.affine 5242495 0 0] := by rfl

theorem paddingFrontLength6 : (paddingFront6.map Block.length).sum = 1048572 := by decide +kernel

theorem paddingValue6 (row : Fin 8388608) (lower : 3146113 ≤ row.val) : Data.GKRSetup.Unified.setupColumn6.get? row.val = some 0 := by
  change Setup.getFromBlocks Data.GKRSetup.Unified.setupColumn6.blocks.toList row.val = _
  rw [UnifiedAllPrefix.Column6.sourceShape, getFromBlocks_append, UnifiedAllPrefix.Column6.originalLength, if_neg (by omega), paddingShape6, getFromBlocks_append, paddingFrontLength6, if_neg (by omega)]
  rw [Setup.getFromBlocks, if_pos (by have := row.isLt; change row.val - 2097541 - 1048572 < 5242495; omega)]
  exact constant_block_get _ _ _ (by have := row.isLt; omega)

column_blocks_part paddingFront7 from Data.GKRSetup.Unified.setupColumn7 start 24670 stop 24671

theorem paddingShape7 : UnifiedAllPrefix.Column7.suffix = paddingFront7 ++ [Block.affine 5242495 0 0] := by rfl

theorem paddingFrontLength7 : (paddingFront7.map Block.length).sum = 1048572 := by decide +kernel

theorem paddingValue7 (row : Fin 8388608) (lower : 3146113 ≤ row.val) : Data.GKRSetup.Unified.setupColumn7.get? row.val = some 0 := by
  change Setup.getFromBlocks Data.GKRSetup.Unified.setupColumn7.blocks.toList row.val = _
  rw [UnifiedAllPrefix.Column7.sourceShape, getFromBlocks_append, UnifiedAllPrefix.Column7.originalLength, if_neg (by omega), paddingShape7, getFromBlocks_append, paddingFrontLength7, if_neg (by omega)]
  rw [Setup.getFromBlocks, if_pos (by have := row.isLt; change row.val - 2097541 - 1048572 < 5242495; omega)]
  exact constant_block_get _ _ _ (by have := row.isLt; omega)

column_blocks_part paddingFront8 from Data.GKRSetup.Unified.setupColumn8 start 1 stop 3

theorem paddingShape8 : UnifiedAllPrefix.Column8.suffix = paddingFront8 ++ [Block.affine 5242495 0 0] := by rfl

theorem paddingFrontLength8 : (paddingFront8.map Block.length).sum = 1048576 := by decide +kernel

theorem paddingValue8 (row : Fin 8388608) (lower : 3146113 ≤ row.val) : Data.GKRSetup.Unified.setupColumn8.get? row.val = some 0 := by
  change Setup.getFromBlocks Data.GKRSetup.Unified.setupColumn8.blocks.toList row.val = _
  rw [UnifiedAllPrefix.Column8.sourceShape, getFromBlocks_append, UnifiedAllPrefix.Column8.originalLength, if_neg (by omega), paddingShape8, getFromBlocks_append, paddingFrontLength8, if_neg (by omega)]
  rw [Setup.getFromBlocks, if_pos (by have := row.isLt; change row.val - 2097537 - 1048576 < 5242495; omega)]
  exact constant_block_get _ _ _ (by have := row.isLt; omega)

column_blocks_part paddingFront9 from Data.GKRSetup.Unified.setupColumn9 start 16 stop 17

theorem paddingShape9 : UnifiedAllPrefix.Column9.suffix = paddingFront9 ++ [Block.affine 5242495 0 0] := by rfl

theorem paddingFrontLength9 : (paddingFront9.map Block.length).sum = 1048576 := by decide +kernel

theorem paddingValue9 (row : Fin 8388608) (lower : 3146113 ≤ row.val) : Data.GKRSetup.Unified.setupColumn9.get? row.val = some 0 := by
  change Setup.getFromBlocks Data.GKRSetup.Unified.setupColumn9.blocks.toList row.val = _
  rw [UnifiedAllPrefix.Column9.sourceShape, getFromBlocks_append, UnifiedAllPrefix.Column9.originalLength, if_neg (by omega), paddingShape9, getFromBlocks_append, paddingFrontLength9, if_neg (by omega)]
  rw [Setup.getFromBlocks, if_pos (by have := row.isLt; change row.val - 2097537 - 1048576 < 5242495; omega)]
  exact constant_block_get _ _ _ (by have := row.isLt; omega)

theorem decoder_tag (row : Fin nativeSetup.imported.data.length)
    (lower : 2097537 ≤ row.val) (upper : row.val < 3146113) : nativeSetup.value row (.generic 9) = 46 := by
  rw [UnifiedTag.tag_value, if_neg (by omega)]
  change (if (row.val - 1) < 131072 then _ else _) = 46
  rw [if_neg (by omega)]
  change (if ((row.val - 1) - 131072) < 65536 then _ else _) = 46
  rw [if_neg (by omega)]
  change (if (((row.val - 1) - 131072) - 65536) < 256 then _ else _) = 46
  rw [if_neg (by omega)]
  change (if ((((row.val - 1) - 131072) - 65536) - 256) < 65536 then _ else _) = 46
  rw [if_neg (by omega)]
  change (if (((((row.val - 1) - 131072) - 65536) - 256) - 65536) < 65536 then _ else _) = 46
  rw [if_neg (by omega)]
  change (if ((((((row.val - 1) - 131072) - 65536) - 256) - 65536) - 65536) < 262144 then _ else _) = 46
  rw [if_neg (by omega)]
  change (if (((((((row.val - 1) - 131072) - 65536) - 256) - 65536) - 65536) - 262144) < 1048576 then _ else _) = 46
  rw [if_neg (by omega)]
  change (if ((((((((row.val - 1) - 131072) - 65536) - 256) - 65536) - 65536) - 262144) - 1048576) < 65536 then _ else _) = 46
  rw [if_neg (by omega)]
  change (if (((((((((row.val - 1) - 131072) - 65536) - 256) - 65536) - 65536) - 262144) - 1048576) - 65536) < 65536 then _ else _) = 46
  rw [if_neg (by omega)]
  change (if ((((((((((row.val - 1) - 131072) - 65536) - 256) - 65536) - 65536) - 262144) - 1048576) - 65536) - 65536) < 65536 then _ else _) = 46
  rw [if_neg (by omega)]
  change (if (((((((((((row.val - 1) - 131072) - 65536) - 256) - 65536) - 65536) - 262144) - 1048576) - 65536) - 65536) - 65536) < 65536 then _ else _) = 46
  rw [if_neg (by omega)]
  change (if ((((((((((((row.val - 1) - 131072) - 65536) - 256) - 65536) - 65536) - 262144) - 1048576) - 65536) - 65536) - 65536) - 65536) < 128 then _ else _) = 46
  rw [if_neg (by omega)]
  change (if (((((((((((((row.val - 1) - 131072) - 65536) - 256) - 65536) - 65536) - 262144) - 1048576) - 65536) - 65536) - 65536) - 65536) - 128) < 65536 then _ else _) = 46
  rw [if_neg (by omega)]
  change (if ((((((((((((((row.val - 1) - 131072) - 65536) - 256) - 65536) - 65536) - 262144) - 1048576) - 65536) - 65536) - 65536) - 65536) - 128) - 65536) < 65536 then _ else _) = 46
  rw [if_neg (by omega)]
  change (if (((((((((((((((row.val - 1) - 131072) - 65536) - 256) - 65536) - 65536) - 262144) - 1048576) - 65536) - 65536) - 65536) - 65536) - 128) - 65536) - 65536) < 65536 then _ else _) = 46
  rw [if_neg (by omega)]
  change (if ((((((((((((((((row.val - 1) - 131072) - 65536) - 256) - 65536) - 65536) - 262144) - 1048576) - 65536) - 65536) - 65536) - 65536) - 128) - 65536) - 65536) - 65536) < 1048576 then _ else _) = 46
  rw [if_pos (by omega)]
  norm_num

theorem padding_row (row : Fin 8388608) (lower : 3146113 ≤ row.val) :
    UnifiedRows.nativeRow row = Vector.replicate 10 0 := by
  apply Vector.ext
  intro column bound
  simp only [UnifiedRows.nativeRow, TableData.row, Vector.getElem_map, Vector.getElem_replicate,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  interval_cases column
  · change ((Setup.signedValue ((Data.GKRSetup.Unified.setupColumn0.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue0 row lower]
    rfl
  · change ((Setup.signedValue ((Data.GKRSetup.Unified.setupColumn1.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue1 row lower]
    rfl
  · change ((Setup.signedValue ((Data.GKRSetup.Unified.setupColumn2.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue2 row lower]
    rfl
  · change ((Setup.signedValue ((Data.GKRSetup.Unified.setupColumn3.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue3 row lower]
    rfl
  · change ((Setup.signedValue ((Data.GKRSetup.Unified.setupColumn4.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue4 row lower]
    rfl
  · change ((Setup.signedValue ((Data.GKRSetup.Unified.setupColumn5.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue5 row lower]
    rfl
  · change ((Setup.signedValue ((Data.GKRSetup.Unified.setupColumn6.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue6 row lower]
    rfl
  · change ((Setup.signedValue ((Data.GKRSetup.Unified.setupColumn7.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue7 row lower]
    rfl
  · change ((Setup.signedValue ((Data.GKRSetup.Unified.setupColumn8.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue8 row lower]
    rfl
  · change ((Setup.signedValue ((Data.GKRSetup.Unified.setupColumn9.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue9 row lower]
    rfl

theorem full_table_refinement {query : Vector Source.BaseField 10}
    (member : (nativeSetup.imported.data.table "Airbender.Native.UnifiedReduced").Contains #[] query)
    (notDecoder : query[9] ≠ 46) : (UnifiedReduced.Setup.importedTable (p := babyBearModulus)).Contains #[] query := by
  obtain ⟨row, equal⟩ := member
  change query = UnifiedRows.nativeRow row at equal
  by_cases beforeDecoder : row.val < 2097537
  · have retained := UnifiedRows.prefix_member ⟨row.val, beforeDecoder⟩
    change (UnifiedReduced.Setup.importedTable (p := babyBearModulus)).Contains #[] (UnifiedRows.nativeRow row) at retained
    exact equal.symm ▸ retained
  · have lower : 3146113 ≤ row.val := by
      by_contra earlier
      have tag := decoder_tag row (by omega) (by omega)
      apply notDecoder
      rw [equal]
      rw [nativeSetup.value_generic row (⟨9, by decide⟩ : Fin 10)] at tag
      simpa only [UnifiedRows.nativeRow, Vector.getElem_map] using tag
    rw [padding_row row lower] at equal
    refine ⟨⟨0, by decide⟩, equal.trans ?_⟩
    decide +kernel

end Airbender.Compiler.ROMNative.UnifiedBoundary
