import Airbender.Proofs.GKRProtocol.ROMNative.SubwordRows

namespace Airbender.Compiler.ROMNative.SubwordBoundary
open Airbender Airbender.Compiler Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := SubwordRows.nativeSetup

theorem paddingPrefix0 : ((Data.GKRSetup.SubwordMemory.setupColumn0.blocks.toList.take 8).map Block.length).sum = 14286849 := by decide +kernel

theorem paddingShape0 : Data.GKRSetup.SubwordMemory.setupColumn0.blocks[8] = Block.affine 2490367 0 0 := by rfl

theorem paddingValue0 (row : Fin 16777216) (lower : 14286849 ≤ row.val) : Data.GKRSetup.SubwordMemory.setupColumn0.get? row.val = some 0 := by
  have actual := column_block_value Data.GKRSetup.SubwordMemory.setupColumn0 ⟨8, by decide +kernel⟩ 14286849 row.val paddingPrefix0 lower (by
    rw [paddingShape0]
    have := row.isLt
    change row.val - 14286849 < 2490367
    omega)
  rw [paddingShape0] at actual
  exact actual.trans (constant_block_get _ _ _ (by have := row.isLt; omega))

theorem paddingPrefix1 : ((Data.GKRSetup.SubwordMemory.setupColumn1.blocks.toList.take 17).map Block.length).sum = 14286849 := by decide +kernel

theorem paddingShape1 : Data.GKRSetup.SubwordMemory.setupColumn1.blocks[17] = Block.affine 2490367 0 0 := by rfl

theorem paddingValue1 (row : Fin 16777216) (lower : 14286849 ≤ row.val) : Data.GKRSetup.SubwordMemory.setupColumn1.get? row.val = some 0 := by
  have actual := column_block_value Data.GKRSetup.SubwordMemory.setupColumn1 ⟨17, by decide +kernel⟩ 14286849 row.val paddingPrefix1 lower (by
    rw [paddingShape1]
    have := row.isLt
    change row.val - 14286849 < 2490367
    omega)
  rw [paddingShape1] at actual
  exact actual.trans (constant_block_get _ _ _ (by have := row.isLt; omega))

theorem paddingPrefix2 : ((Data.GKRSetup.SubwordMemory.setupColumn2.blocks.toList.take 16).map Block.length).sum = 14286849 := by decide +kernel

theorem paddingShape2 : Data.GKRSetup.SubwordMemory.setupColumn2.blocks[16] = Block.affine 2490367 0 0 := by rfl

theorem paddingValue2 (row : Fin 16777216) (lower : 14286849 ≤ row.val) : Data.GKRSetup.SubwordMemory.setupColumn2.get? row.val = some 0 := by
  have actual := column_block_value Data.GKRSetup.SubwordMemory.setupColumn2 ⟨16, by decide +kernel⟩ 14286849 row.val paddingPrefix2 lower (by
    rw [paddingShape2]
    have := row.isLt
    change row.val - 14286849 < 2490367
    omega)
  rw [paddingShape2] at actual
  exact actual.trans (constant_block_get _ _ _ (by have := row.isLt; omega))

theorem paddingPrefix3 : ((Data.GKRSetup.SubwordMemory.setupColumn3.blocks.toList.take 2).map Block.length).sum = 14286849 := by decide +kernel

theorem paddingShape3 : Data.GKRSetup.SubwordMemory.setupColumn3.blocks[2] = Block.affine 2490367 0 0 := by rfl

theorem paddingValue3 (row : Fin 16777216) (lower : 14286849 ≤ row.val) : Data.GKRSetup.SubwordMemory.setupColumn3.get? row.val = some 0 := by
  have actual := column_block_value Data.GKRSetup.SubwordMemory.setupColumn3 ⟨2, by decide +kernel⟩ 14286849 row.val paddingPrefix3 lower (by
    rw [paddingShape3]
    have := row.isLt
    change row.val - 14286849 < 2490367
    omega)
  rw [paddingShape3] at actual
  exact actual.trans (constant_block_get _ _ _ (by have := row.isLt; omega))

theorem paddingPrefix4 : ((Data.GKRSetup.SubwordMemory.setupColumn4.blocks.toList.take 2).map Block.length).sum = 14286849 := by decide +kernel

theorem paddingShape4 : Data.GKRSetup.SubwordMemory.setupColumn4.blocks[2] = Block.affine 2490367 0 0 := by rfl

theorem paddingValue4 (row : Fin 16777216) (lower : 14286849 ≤ row.val) : Data.GKRSetup.SubwordMemory.setupColumn4.get? row.val = some 0 := by
  have actual := column_block_value Data.GKRSetup.SubwordMemory.setupColumn4 ⟨2, by decide +kernel⟩ 14286849 row.val paddingPrefix4 lower (by
    rw [paddingShape4]
    have := row.isLt
    change row.val - 14286849 < 2490367
    omega)
  rw [paddingShape4] at actual
  exact actual.trans (constant_block_get _ _ _ (by have := row.isLt; omega))

theorem paddingPrefix5 : ((Data.GKRSetup.SubwordMemory.setupColumn5.blocks.toList.take 2).map Block.length).sum = 14286849 := by decide +kernel

theorem paddingShape5 : Data.GKRSetup.SubwordMemory.setupColumn5.blocks[2] = Block.affine 2490367 0 0 := by rfl

theorem paddingValue5 (row : Fin 16777216) (lower : 14286849 ≤ row.val) : Data.GKRSetup.SubwordMemory.setupColumn5.get? row.val = some 0 := by
  have actual := column_block_value Data.GKRSetup.SubwordMemory.setupColumn5 ⟨2, by decide +kernel⟩ 14286849 row.val paddingPrefix5 lower (by
    rw [paddingShape5]
    have := row.isLt
    change row.val - 14286849 < 2490367
    omega)
  rw [paddingShape5] at actual
  exact actual.trans (constant_block_get _ _ _ (by have := row.isLt; omega))

theorem paddingPrefix6 : ((Data.GKRSetup.SubwordMemory.setupColumn6.blocks.toList.take 2).map Block.length).sum = 14286849 := by decide +kernel

theorem paddingShape6 : Data.GKRSetup.SubwordMemory.setupColumn6.blocks[2] = Block.affine 2490367 0 0 := by rfl

theorem paddingValue6 (row : Fin 16777216) (lower : 14286849 ≤ row.val) : Data.GKRSetup.SubwordMemory.setupColumn6.get? row.val = some 0 := by
  have actual := column_block_value Data.GKRSetup.SubwordMemory.setupColumn6 ⟨2, by decide +kernel⟩ 14286849 row.val paddingPrefix6 lower (by
    rw [paddingShape6]
    have := row.isLt
    change row.val - 14286849 < 2490367
    omega)
  rw [paddingShape6] at actual
  exact actual.trans (constant_block_get _ _ _ (by have := row.isLt; omega))

theorem paddingPrefix7 : ((Data.GKRSetup.SubwordMemory.setupColumn7.blocks.toList.take 2).map Block.length).sum = 14286849 := by decide +kernel

theorem paddingShape7 : Data.GKRSetup.SubwordMemory.setupColumn7.blocks[2] = Block.affine 2490367 0 0 := by rfl

theorem paddingValue7 (row : Fin 16777216) (lower : 14286849 ≤ row.val) : Data.GKRSetup.SubwordMemory.setupColumn7.get? row.val = some 0 := by
  have actual := column_block_value Data.GKRSetup.SubwordMemory.setupColumn7 ⟨2, by decide +kernel⟩ 14286849 row.val paddingPrefix7 lower (by
    rw [paddingShape7]
    have := row.isLt
    change row.val - 14286849 < 2490367
    omega)
  rw [paddingShape7] at actual
  exact actual.trans (constant_block_get _ _ _ (by have := row.isLt; omega))

theorem paddingPrefix8 : ((Data.GKRSetup.SubwordMemory.setupColumn8.blocks.toList.take 8).map Block.length).sum = 14286849 := by decide +kernel

theorem paddingShape8 : Data.GKRSetup.SubwordMemory.setupColumn8.blocks[8] = Block.affine 2490367 0 0 := by rfl

theorem paddingValue8 (row : Fin 16777216) (lower : 14286849 ≤ row.val) : Data.GKRSetup.SubwordMemory.setupColumn8.get? row.val = some 0 := by
  have actual := column_block_value Data.GKRSetup.SubwordMemory.setupColumn8 ⟨8, by decide +kernel⟩ 14286849 row.val paddingPrefix8 lower (by
    rw [paddingShape8]
    have := row.isLt
    change row.val - 14286849 < 2490367
    omega)
  rw [paddingShape8] at actual
  exact actual.trans (constant_block_get _ _ _ (by have := row.isLt; omega))

theorem decoderPrefix : ((Data.GKRSetup.SubwordMemory.setupColumn8.blocks.toList.take 7).map Block.length).sum = 13238273 := by decide +kernel

theorem decoderShape : Data.GKRSetup.SubwordMemory.setupColumn8.blocks[7] = Block.affine 1048576 46 0 := by rfl

theorem decoder_tag (row : Fin nativeSetup.imported.data.length)
    (lower : 13238273 ≤ row.val) (upper : row.val < 14286849) : nativeSetup.value row (.generic 8) = 46 := by
  rw [nativeSetup.generic_cell_value row (⟨8, by decide⟩ : Fin 9)]
  simp only [show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  have actual := column_block_value Data.GKRSetup.SubwordMemory.setupColumn8 ⟨7, by decide +kernel⟩ 13238273 row.val decoderPrefix lower (by
    rw [decoderShape]
    change row.val - 13238273 < 1048576
    omega)
  rw [decoderShape] at actual
  change (((Data.GKRSetup.SubwordMemory.setupColumn8.get? row.val).getD 0) : Source.BaseField) = 46
  rw [actual, constant_block_get _ _ _ (by omega)]
  rfl

theorem padding_row (row : Fin 16777216) (lower : 14286849 ≤ row.val) :
    SubwordRows.nativeRow row = Vector.replicate 9 0 := by
  apply Vector.ext
  intro column bound
  simp only [SubwordRows.nativeRow, TableData.row, Vector.getElem_map, Vector.getElem_replicate,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  interval_cases column
  · change ((Setup.signedValue ((Data.GKRSetup.SubwordMemory.setupColumn0.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue0 row lower]
    rfl
  · change ((Setup.signedValue ((Data.GKRSetup.SubwordMemory.setupColumn1.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue1 row lower]
    rfl
  · change ((Setup.signedValue ((Data.GKRSetup.SubwordMemory.setupColumn2.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue2 row lower]
    rfl
  · change ((Setup.signedValue ((Data.GKRSetup.SubwordMemory.setupColumn3.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue3 row lower]
    rfl
  · change ((Setup.signedValue ((Data.GKRSetup.SubwordMemory.setupColumn4.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue4 row lower]
    rfl
  · change ((Setup.signedValue ((Data.GKRSetup.SubwordMemory.setupColumn5.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue5 row lower]
    rfl
  · change ((Setup.signedValue ((Data.GKRSetup.SubwordMemory.setupColumn6.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue6 row lower]
    rfl
  · change ((Setup.signedValue ((Data.GKRSetup.SubwordMemory.setupColumn7.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue7 row lower]
    rfl
  · change ((Setup.signedValue ((Data.GKRSetup.SubwordMemory.setupColumn8.get? row.val).getD 0)) : Source.BaseField) = 0
    rw [paddingValue8 row lower]
    rfl

theorem full_table_refinement {query : Vector Source.BaseField 9}
    (member : (nativeSetup.imported.data.table "Airbender.Native.SubwordMemory").Contains #[] query)
    (notDecoder : query[8] ≠ 46) : (Verification.importedSubwordTable (p := babyBearModulus)).Contains #[] query := by
  obtain ⟨row, equal⟩ := member
  change query = SubwordRows.nativeRow row at equal
  by_cases beforeDecoder : row.val < 13238273
  · exact ⟨⟨row.val, beforeDecoder⟩, equal.trans (SubwordRows.prefix_row ⟨row.val, beforeDecoder⟩)⟩
  · have lower : 14286849 ≤ row.val := by
      by_contra earlier
      have tag := decoder_tag row (by omega) (by omega)
      apply notDecoder
      rw [equal]
      rw [nativeSetup.value_generic row (⟨8, by decide⟩ : Fin 9)] at tag
      simpa only [SubwordRows.nativeRow, Vector.getElem_map] using tag
    rw [padding_row row lower] at equal
    refine ⟨⟨0, by decide⟩, equal.trans ?_⟩
    decide +kernel

end Airbender.Compiler.ROMNative.SubwordBoundary
