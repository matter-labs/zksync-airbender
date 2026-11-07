import Airbender.Proofs.GKRProtocol.FixedSetupNative.MulDiv

namespace Airbender.Compiler.FixedSetupNative.MulDiv
open Airbender Airbender.Compiler
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def nativeValueColumn := nativeSetup.imported.data.columns[1]
def zeroValueColumn := Verification.regZeroData.columns[1]

private theorem zero_first : nativeValueColumn.get? 0 = zeroValueColumn.get? 0 := by decide +kernel
private theorem native_prefix1 : ((nativeValueColumn.blocks.toList.take 1).map Setup.Block.length).sum = 1 := by decide +kernel
private theorem zero_prefix1 : ((zeroValueColumn.blocks.toList.take 1).map Setup.Block.length).sum = 1 := by decide +kernel

theorem regZeroData1_value (index : Fin Verification.regZeroData.length) :
    nativeValueColumn.get? index.val = zeroValueColumn.get? index.val := by
  have bound : index.val < 131072 := index.isLt
  by_cases first : index.val = 0
  · rw [first]
    exact zero_first
  · have lower : 1 ≤ index.val := by omega
    have left := column_block_value nativeValueColumn (⟨1, by decide⟩) 1 index.val native_prefix1 lower
      (by change index.val - 1 < 131072; omega)
    have right := column_block_value zeroValueColumn (⟨1, by decide⟩) 1 index.val zero_prefix1 lower
      (by change index.val - 1 < 131071; omega)
    rw [left, right]
    change (Setup.Block.affine 131072 0 0).get? (index.val - 1) =
      (Setup.Block.affine 131071 0 0).get? (index.val - 1)
    rw [constant_block_get _ _ _ (by omega), constant_block_get _ _ _ (by omega)]


def lowByteValueColumn := Verification.lowByteData.columns[1]
def nativeKeyColumn := nativeSetup.imported.data.columns[0]

private theorem low_byte_first : nativeValueColumn.get? 204800 = lowByteValueColumn.get? 0 := by decide +kernel
private theorem source_prefix4 : ((nativeValueColumn.blocks.toList.take 4).map Setup.Block.length).sum = 204801 := by decide +kernel
private theorem source_prefix5 : ((nativeValueColumn.blocks.toList.take 5).map Setup.Block.length).sum = 270081 := by decide +kernel
private theorem low_byte_prefix1 : ((lowByteValueColumn.blocks.toList.take 1).map Setup.Block.length).sum = 1 := by decide +kernel
private theorem low_byte_prefix2 : ((lowByteValueColumn.blocks.toList.take 2).map Setup.Block.length).sum = 65281 := by decide +kernel
private theorem source_key_prefix2 : ((nativeKeyColumn.blocks.toList.take 2).map Setup.Block.length).sum = 196608 := by decide +kernel

theorem lowByteData1_value (index : Fin Verification.lowByteData.length) :
    nativeValueColumn.get? (204800 + index.val) = lowByteValueColumn.get? index.val := by
  have bound : index.val < 65536 := index.isLt
  by_cases first : index.val = 0
  · rw [first]
    exact low_byte_first
  · by_cases middle : index.val < 65281
    · have left := column_block_value nativeValueColumn (⟨4, by decide⟩) 204801 (204800 + index.val) source_prefix4
        (by omega) (by change 204800 + index.val - 204801 < 65280; omega)
      have right := column_block_value lowByteValueColumn (⟨1, by decide⟩) 1 index.val low_byte_prefix1
        (by omega) (by change index.val - 1 < 65280; omega)
      have relative : 204800 + index.val - 204801 = index.val - 1 := by omega
      rw [left, right, relative]
      rfl
    · have left := column_block_value nativeValueColumn (⟨5, by decide⟩) 270081 (204800 + index.val) source_prefix5
        (by omega) (by change 204800 + index.val - 270081 < 255; omega)
      have right := column_block_value lowByteValueColumn (⟨2, by decide⟩) 65281 index.val low_byte_prefix2
        (by omega) (by change index.val - 65281 < 255; omega)
      have relative : 204800 + index.val - 270081 = index.val - 65281 := by omega
      rw [left, right, relative]
      rfl

theorem range13_key_value (index : Fin 8192) :
    nativeKeyColumn.get? (196608 + index.val) = some index.val := by
  have left := column_block_value nativeKeyColumn (⟨2, by decide⟩) 196608 (196608 + index.val) source_key_prefix2
    (by omega) (by change 196608 + index.val - 196608 < 8192; have := index.isLt; omega)
  have relative : 196608 + index.val - 196608 = index.val := by omega
  rw [left, relative]
  change (Setup.Block.affine 8192 0 1).get? index.val = some index.val
  simp [Setup.Block.get?, Setup.Block.length, index.isLt]

end Airbender.Compiler.FixedSetupNative.MulDiv
