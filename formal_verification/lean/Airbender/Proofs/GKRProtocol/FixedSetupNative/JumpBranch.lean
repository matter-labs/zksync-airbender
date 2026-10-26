import Airbender.Proofs.GKRProtocol.ColumnSlices
import Airbender.Proofs.GKRProtocol.TaggedSetup
import Airbender.Proofs.GKRProtocol.MaterializedNative.JumpBranchUncached
import Airbender.Review.Helpers.Tables.PairData

namespace Airbender.Compiler.FixedSetupNative.JumpBranch
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

abbrev nativeSetup := Airbender.Compiler.MaterializedNative.JumpBranchUncached.native.model

def regZeroData0Front : List Setup.Block := nativeSetup.imported.data.columns[0].blocks.toList.take 0
def regZeroData0Back : List Setup.Block := nativeSetup.imported.data.columns[0].blocks.toList.drop 1

theorem regZeroData0Shape : nativeSetup.imported.data.columns[0].blocks.toList =
    regZeroData0Front ++ (Verification.regZeroData.columns[0].blocks.toList ++ regZeroData0Back) := by decide +kernel

theorem regZeroData0Prefix : (regZeroData0Front.map Setup.Block.length).sum = 0 := by decide +kernel

theorem regZeroData0Length : (Verification.regZeroData.columns[0].blocks.toList.map Setup.Block.length).sum = 131072 := by decide +kernel

theorem regZeroData0_value (index : Fin Verification.regZeroData.length) :
    nativeSetup.imported.data.columns[0].get? (0 + index.val) = Verification.regZeroData.columns[0].get? index.val :=
  column_slice_value nativeSetup.imported.data.columns[0] Verification.regZeroData.columns[0] regZeroData0Front regZeroData0Back 0 131072
    regZeroData0Shape regZeroData0Prefix regZeroData0Length index.val index.isLt

def jumpCleanupData0Front : List Setup.Block := nativeSetup.imported.data.columns[0].blocks.toList.take 1
def jumpCleanupData0Back : List Setup.Block := nativeSetup.imported.data.columns[0].blocks.toList.drop 2

theorem jumpCleanupData0Shape : nativeSetup.imported.data.columns[0].blocks.toList =
    jumpCleanupData0Front ++ (Verification.jumpCleanupData.columns[0].blocks.toList ++ jumpCleanupData0Back) := by decide +kernel

theorem jumpCleanupData0Prefix : (jumpCleanupData0Front.map Setup.Block.length).sum = 131072 := by decide +kernel

theorem jumpCleanupData0Length : (Verification.jumpCleanupData.columns[0].blocks.toList.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem jumpCleanupData0_value (index : Fin Verification.jumpCleanupData.length) :
    nativeSetup.imported.data.columns[0].get? (131072 + index.val) = Verification.jumpCleanupData.columns[0].get? index.val :=
  column_slice_value nativeSetup.imported.data.columns[0] Verification.jumpCleanupData.columns[0] jumpCleanupData0Front jumpCleanupData0Back 131072 65536
    jumpCleanupData0Shape jumpCleanupData0Prefix jumpCleanupData0Length index.val index.isLt

def signData0Front : List Setup.Block := nativeSetup.imported.data.columns[0].blocks.toList.take 2
def signData0Back : List Setup.Block := nativeSetup.imported.data.columns[0].blocks.toList.drop 3

theorem signData0Shape : nativeSetup.imported.data.columns[0].blocks.toList =
    signData0Front ++ (Verification.signData.columns[0].blocks.toList ++ signData0Back) := by decide +kernel

theorem signData0Prefix : (signData0Front.map Setup.Block.length).sum = 196608 := by decide +kernel

theorem signData0Length : (Verification.signData.columns[0].blocks.toList.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem signData0_value (index : Fin Verification.signData.length) :
    nativeSetup.imported.data.columns[0].get? (196608 + index.val) = Verification.signData.columns[0].get? index.val :=
  column_slice_value nativeSetup.imported.data.columns[0] Verification.signData.columns[0] signData0Front signData0Back 196608 65536
    signData0Shape signData0Prefix signData0Length index.val index.isLt

def conditionalData0Front : List Setup.Block := nativeSetup.imported.data.columns[0].blocks.toList.take 3
def conditionalData0Back : List Setup.Block := nativeSetup.imported.data.columns[0].blocks.toList.drop 4

theorem conditionalData0Shape : nativeSetup.imported.data.columns[0].blocks.toList =
    conditionalData0Front ++ (Verification.conditionalData.columns[0].blocks.toList ++ conditionalData0Back) := by decide +kernel

theorem conditionalData0Prefix : (conditionalData0Front.map Setup.Block.length).sum = 262144 := by decide +kernel

theorem conditionalData0Length : (Verification.conditionalData.columns[0].blocks.toList.map Setup.Block.length).sum = 4194304 := by decide +kernel

theorem conditionalData0_value (index : Fin Verification.conditionalData.length) :
    nativeSetup.imported.data.columns[0].get? (262144 + index.val) = Verification.conditionalData.columns[0].get? index.val :=
  column_slice_value nativeSetup.imported.data.columns[0] Verification.conditionalData.columns[0] conditionalData0Front conditionalData0Back 262144 4194304
    conditionalData0Shape conditionalData0Prefix conditionalData0Length index.val index.isLt

def conditionalData1Front : List Setup.Block := nativeSetup.imported.data.columns[1].blocks.toList.take 5
def conditionalData1Back : List Setup.Block := nativeSetup.imported.data.columns[1].blocks.toList.drop 52

theorem conditionalData1Shape : nativeSetup.imported.data.columns[1].blocks.toList =
    conditionalData1Front ++ (Verification.conditionalData.columns[1].blocks.toList ++ conditionalData1Back) := by decide +kernel

theorem conditionalData1Prefix : (conditionalData1Front.map Setup.Block.length).sum = 262144 := by decide +kernel

theorem conditionalData1Length : (Verification.conditionalData.columns[1].blocks.toList.map Setup.Block.length).sum = 4194304 := by decide +kernel

theorem conditionalData1_value (index : Fin Verification.conditionalData.length) :
    nativeSetup.imported.data.columns[1].get? (262144 + index.val) = Verification.conditionalData.columns[1].get? index.val :=
  column_slice_value nativeSetup.imported.data.columns[1] Verification.conditionalData.columns[1] conditionalData1Front conditionalData1Back 262144 4194304
    conditionalData1Shape conditionalData1Prefix conditionalData1Length index.val index.isLt

def tagSegments : List (Nat × Nat) :=
  [(131072, 1), (65536, 2), (65536, 5), (4194304, 31), (1048576, 46), (11272192, 0)]

theorem tag_shape : nativeSetup.imported.data.columns[9].blocks.toList =
    tagSegments.map (fun entry => Setup.Block.affine entry.1 entry.2 0) := by decide +kernel

theorem tag_value (row : Fin nativeSetup.imported.data.length) :
    nativeSetup.value row (.generic 9) = constantTagValue tagSegments row.val := by
  have bridge := nativeSetup.constant_tag_value (⟨9, by decide⟩ : Fin 10) tagSegments tag_shape row
  simpa only [show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add] using bridge

theorem tag1_region (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 9) = 1) :
    0 ≤ row.val ∧ row.val < 131072 := by
  have rowBound : row.val < 16777216 := row.isLt
  rw [tag_value] at selected
  simp only [tagSegments, constantTagValue] at selected
  split_ifs at selected
  all_goals first
    | omega
    | exact False.elim ((by decide +kernel : (2 : Source.BaseField) ≠ 1) selected)
    | exact False.elim ((by decide +kernel : (5 : Source.BaseField) ≠ 1) selected)
    | exact False.elim ((by decide +kernel : (31 : Source.BaseField) ≠ 1) selected)
    | exact False.elim ((by decide +kernel : (46 : Source.BaseField) ≠ 1) selected)
    | exact False.elim ((by decide +kernel : (0 : Source.BaseField) ≠ 1) selected)

theorem tag2_region (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 9) = 2) :
    131072 ≤ row.val ∧ row.val < 196608 := by
  have rowBound : row.val < 16777216 := row.isLt
  rw [tag_value] at selected
  simp only [tagSegments, constantTagValue] at selected
  split_ifs at selected
  all_goals first
    | omega
    | exact False.elim ((by decide +kernel : (1 : Source.BaseField) ≠ 2) selected)
    | exact False.elim ((by decide +kernel : (5 : Source.BaseField) ≠ 2) selected)
    | exact False.elim ((by decide +kernel : (31 : Source.BaseField) ≠ 2) selected)
    | exact False.elim ((by decide +kernel : (46 : Source.BaseField) ≠ 2) selected)
    | exact False.elim ((by decide +kernel : (0 : Source.BaseField) ≠ 2) selected)

theorem tag5_region (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 9) = 5) :
    196608 ≤ row.val ∧ row.val < 262144 := by
  have rowBound : row.val < 16777216 := row.isLt
  rw [tag_value] at selected
  simp only [tagSegments, constantTagValue] at selected
  split_ifs at selected
  all_goals first
    | omega
    | exact False.elim ((by decide +kernel : (1 : Source.BaseField) ≠ 5) selected)
    | exact False.elim ((by decide +kernel : (2 : Source.BaseField) ≠ 5) selected)
    | exact False.elim ((by decide +kernel : (31 : Source.BaseField) ≠ 5) selected)
    | exact False.elim ((by decide +kernel : (46 : Source.BaseField) ≠ 5) selected)
    | exact False.elim ((by decide +kernel : (0 : Source.BaseField) ≠ 5) selected)

theorem tag31_region (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 9) = 31) :
    262144 ≤ row.val ∧ row.val < 4456448 := by
  have rowBound : row.val < 16777216 := row.isLt
  rw [tag_value] at selected
  simp only [tagSegments, constantTagValue] at selected
  split_ifs at selected
  all_goals first
    | omega
    | exact False.elim ((by decide +kernel : (1 : Source.BaseField) ≠ 31) selected)
    | exact False.elim ((by decide +kernel : (2 : Source.BaseField) ≠ 31) selected)
    | exact False.elim ((by decide +kernel : (5 : Source.BaseField) ≠ 31) selected)
    | exact False.elim ((by decide +kernel : (46 : Source.BaseField) ≠ 31) selected)
    | exact False.elim ((by decide +kernel : (0 : Source.BaseField) ≠ 31) selected)

theorem tag46_region (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 9) = 46) :
    4456448 ≤ row.val ∧ row.val < 5505024 := by
  have rowBound : row.val < 16777216 := row.isLt
  rw [tag_value] at selected
  simp only [tagSegments, constantTagValue] at selected
  split_ifs at selected
  all_goals first
    | omega
    | exact False.elim ((by decide +kernel : (1 : Source.BaseField) ≠ 46) selected)
    | exact False.elim ((by decide +kernel : (2 : Source.BaseField) ≠ 46) selected)
    | exact False.elim ((by decide +kernel : (5 : Source.BaseField) ≠ 46) selected)
    | exact False.elim ((by decide +kernel : (31 : Source.BaseField) ≠ 46) selected)
    | exact False.elim ((by decide +kernel : (0 : Source.BaseField) ≠ 46) selected)

theorem tag0_region (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 9) = 0) :
    5505024 ≤ row.val ∧ row.val < 16777216 := by
  have rowBound : row.val < 16777216 := row.isLt
  rw [tag_value] at selected
  simp only [tagSegments, constantTagValue] at selected
  split_ifs at selected
  all_goals first
    | omega
    | exact False.elim ((by decide +kernel : (1 : Source.BaseField) ≠ 0) selected)
    | exact False.elim ((by decide +kernel : (2 : Source.BaseField) ≠ 0) selected)
    | exact False.elim ((by decide +kernel : (5 : Source.BaseField) ≠ 0) selected)
    | exact False.elim ((by decide +kernel : (31 : Source.BaseField) ≠ 0) selected)
    | exact False.elim ((by decide +kernel : (46 : Source.BaseField) ≠ 0) selected)

end Airbender.Compiler.FixedSetupNative.JumpBranch
