import Airbender.Proofs.GKRProtocol.FixedSetupNative.JumpBranch

namespace Airbender.Compiler.FixedSetupNative.JumpBranch
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
      (by change index.val - 1 < 131073; omega)
    have right := column_block_value zeroValueColumn (⟨1, by decide⟩) 1 index.val zero_prefix1 lower
      (by change index.val - 1 < 131071; omega)
    rw [left, right]
    change (Setup.Block.affine 131073 0 0).get? (index.val - 1) =
      (Setup.Block.affine 131071 0 0).get? (index.val - 1)
    rw [constant_block_get _ _ _ (by omega), constant_block_get _ _ _ (by omega)]


def cleanupValueColumn := Verification.jumpCleanupData.columns[1]
def nativeCleanupColumn := nativeSetup.imported.data.columns[2]
def cleanupDataColumn := Verification.jumpCleanupData.columns[2]
def signValueColumn := Verification.signData.columns[1]

private theorem cleanup_source_prefix1 : ((nativeCleanupColumn.blocks.toList.take 1).map Setup.Block.length).sum = 131076 := by decide +kernel
private theorem cleanup_target_prefix1 : ((cleanupDataColumn.blocks.toList.take 1).map Setup.Block.length).sum = 4 := by decide +kernel
private theorem value_source_prefix2 : ((nativeValueColumn.blocks.toList.take 2).map Setup.Block.length).sum = 131074 := by decide +kernel
private theorem cleanup_value_prefix1 : ((cleanupValueColumn.blocks.toList.take 1).map Setup.Block.length).sum = 2 := by decide +kernel
private theorem value_source_prefix3 : ((nativeValueColumn.blocks.toList.take 3).map Setup.Block.length).sum = 196610 := by decide +kernel
private theorem value_source_prefix4 : ((nativeValueColumn.blocks.toList.take 4).map Setup.Block.length).sum = 229376 := by decide +kernel
private theorem sign_prefix1 : ((signValueColumn.blocks.toList.take 1).map Setup.Block.length).sum = 2 := by decide +kernel
private theorem sign_prefix2 : ((signValueColumn.blocks.toList.take 2).map Setup.Block.length).sum = 32768 := by decide +kernel

theorem jumpCleanupData2_value (index : Fin Verification.jumpCleanupData.length) :
    nativeCleanupColumn.get? (131072 + index.val) = cleanupDataColumn.get? index.val := by
  have bound : index.val < 65536 := index.isLt
  by_cases first : index.val < 4
  · have left := column_block_value nativeCleanupColumn (⟨0, by decide⟩) 0 (131072 + index.val) rfl (Nat.zero_le _)
      (by change 131072 + index.val - 0 < 131076; omega)
    have right := column_block_value cleanupDataColumn (⟨0, by decide⟩) 0 index.val rfl (Nat.zero_le _)
      (by change index.val - 0 < 4; omega)
    rw [left, right]
    change (Setup.Block.affine 131076 0 0).get? (131072 + index.val) =
      (Setup.Block.affine 4 0 0).get? index.val
    rw [constant_block_get _ _ _ (by omega), constant_block_get _ _ _ first]
  · have left := column_block_value nativeCleanupColumn (⟨1, by decide⟩) 131076 (131072 + index.val) cleanup_source_prefix1
      (by omega) (by change 131072 + index.val - 131076 < 65532; omega)
    have right := column_block_value cleanupDataColumn (⟨1, by decide⟩) 4 index.val cleanup_target_prefix1
      (by omega) (by change index.val - 4 < 65532; omega)
    have relative : 131072 + index.val - 131076 = index.val - 4 := by omega
    rw [left, right, relative]
    rfl

theorem jumpCleanupData1_value (index : Fin Verification.jumpCleanupData.length) :
    nativeValueColumn.get? (131072 + index.val) = cleanupValueColumn.get? index.val := by
  have bound : index.val < 65536 := index.isLt
  by_cases first : index.val < 2
  · have left := column_block_value nativeValueColumn (⟨1, by decide⟩) 1 (131072 + index.val) native_prefix1
      (by omega) (by change 131072 + index.val - 1 < 131073; omega)
    have right := column_block_value cleanupValueColumn (⟨0, by decide⟩) 0 index.val rfl (Nat.zero_le _)
      (by change index.val - 0 < 2; omega)
    rw [left, right]
    change (Setup.Block.affine 131073 0 0).get? (131072 + index.val - 1) =
      (Setup.Block.affine 2 0 0).get? index.val
    rw [constant_block_get _ _ _ (by omega), constant_block_get _ _ _ first]
  · by_cases middle : index.val < 65534
    · have left := column_block_value nativeValueColumn (⟨2, by decide⟩) 131074 (131072 + index.val) value_source_prefix2
        (by omega) (by change 131072 + index.val - 131074 < 65536; omega)
      have right := column_block_value cleanupValueColumn (⟨1, by decide⟩) 2 index.val cleanup_value_prefix1
        (by omega) (by change index.val - 2 < 65532; omega)
      have relative : 131072 + index.val - 131074 = index.val - 2 := by omega
      rw [left, right, relative]
      change (Setup.Block.periodic 16384 0 #[1, 1, 0, 0]).get? (index.val - 2) =
        (Setup.Block.periodic 16383 0 #[1, 1, 0, 0]).get? (index.val - 2)
      exact periodic_block_overlap _ _ _ _ _ (by change index.val - 2 < 65536; omega)
        (by change index.val - 2 < 65532; omega)
    · have last : index.val = 65534 ∨ index.val = 65535 := by omega
      rcases last with last | last
      · rw [last]
        decide +kernel
      · rw [last]
        decide +kernel

theorem signData1_value (index : Fin Verification.signData.length) :
    nativeValueColumn.get? (196608 + index.val) = signValueColumn.get? index.val := by
  have bound : index.val < 65536 := index.isLt
  by_cases first : index.val < 2
  · have small : index.val = 0 ∨ index.val = 1 := by omega
    rcases small with small | small
    · rw [small]
      decide +kernel
    · rw [small]
      decide +kernel
  · by_cases lower : index.val < 32768
    · have left := column_block_value nativeValueColumn (⟨3, by decide⟩) 196610 (196608 + index.val) value_source_prefix3
        (by omega) (by change 196608 + index.val - 196610 < 32766; omega)
      have right := column_block_value signValueColumn (⟨1, by decide⟩) 2 index.val sign_prefix1
        (by omega) (by change index.val - 2 < 32766; omega)
      have relative : 196608 + index.val - 196610 = index.val - 2 := by omega
      rw [left, right, relative]
      rfl
    · have left := column_block_value nativeValueColumn (⟨4, by decide⟩) 229376 (196608 + index.val) value_source_prefix4
        (by omega) (by change 196608 + index.val - 229376 < 32768; omega)
      have right := column_block_value signValueColumn (⟨2, by decide⟩) 32768 index.val sign_prefix2
        (by omega) (by change index.val - 32768 < 32768; omega)
      have relative : 196608 + index.val - 229376 = index.val - 32768 := by omega
      rw [left, right, relative]
      rfl

end Airbender.Compiler.FixedSetupNative.JumpBranch
