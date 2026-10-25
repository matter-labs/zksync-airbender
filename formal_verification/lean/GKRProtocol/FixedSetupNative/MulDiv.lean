import GKRProtocol.ColumnSlices
import GKRProtocol.TaggedSetup
import GKRProtocol.MaterializedNative.MulDivUncached
import Airbender.Review.Helpers.Tables.PairData

namespace Airbender.Compiler.FixedSetupNative.MulDiv
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

abbrev nativeSetup := Airbender.Compiler.MaterializedNative.MulDivUncached.native.model

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

def lowByteData0Front : List Setup.Block := nativeSetup.imported.data.columns[0].blocks.toList.take 3
def lowByteData0Back : List Setup.Block := nativeSetup.imported.data.columns[0].blocks.toList.drop 4

theorem lowByteData0Shape : nativeSetup.imported.data.columns[0].blocks.toList =
    lowByteData0Front ++ (Verification.lowByteData.columns[0].blocks.toList ++ lowByteData0Back) := by decide +kernel

theorem lowByteData0Prefix : (lowByteData0Front.map Setup.Block.length).sum = 204800 := by decide +kernel

theorem lowByteData0Length : (Verification.lowByteData.columns[0].blocks.toList.map Setup.Block.length).sum = 65536 := by decide +kernel

theorem lowByteData0_value (index : Fin Verification.lowByteData.length) :
    nativeSetup.imported.data.columns[0].get? (204800 + index.val) = Verification.lowByteData.columns[0].get? index.val :=
  column_slice_value nativeSetup.imported.data.columns[0] Verification.lowByteData.columns[0] lowByteData0Front lowByteData0Back 204800 65536
    lowByteData0Shape lowByteData0Prefix lowByteData0Length index.val index.isLt

def tagSegments : List (Nat × Nat) :=
  [(131072, 1), (65536, 10), (8192, 26), (65536, 41), (1048576, 46), (7069696, 0)]

theorem tag_shape : nativeSetup.imported.data.columns[8].blocks.toList =
    tagSegments.map (fun entry => Setup.Block.affine entry.1 entry.2 0) := by decide +kernel

theorem tag_value (row : Fin nativeSetup.imported.data.length) :
    nativeSetup.value row (.generic 8) = constantTagValue tagSegments row.val := by
  have bridge := nativeSetup.constant_tag_value (⟨8, by decide⟩ : Fin 9) tagSegments tag_shape row
  simpa only [show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add] using bridge

theorem tag1_region (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 8) = 1) :
    0 ≤ row.val ∧ row.val < 131072 := by
  have rowBound : row.val < 8388608 := row.isLt
  rw [tag_value] at selected
  simp only [tagSegments, constantTagValue] at selected
  split_ifs at selected
  all_goals first
    | omega
    | exact False.elim ((by decide +kernel : (10 : Source.BaseField) ≠ 1) selected)
    | exact False.elim ((by decide +kernel : (26 : Source.BaseField) ≠ 1) selected)
    | exact False.elim ((by decide +kernel : (41 : Source.BaseField) ≠ 1) selected)
    | exact False.elim ((by decide +kernel : (46 : Source.BaseField) ≠ 1) selected)
    | exact False.elim ((by decide +kernel : (0 : Source.BaseField) ≠ 1) selected)

theorem tag10_region (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 8) = 10) :
    131072 ≤ row.val ∧ row.val < 196608 := by
  have rowBound : row.val < 8388608 := row.isLt
  rw [tag_value] at selected
  simp only [tagSegments, constantTagValue] at selected
  split_ifs at selected
  all_goals first
    | omega
    | exact False.elim ((by decide +kernel : (1 : Source.BaseField) ≠ 10) selected)
    | exact False.elim ((by decide +kernel : (26 : Source.BaseField) ≠ 10) selected)
    | exact False.elim ((by decide +kernel : (41 : Source.BaseField) ≠ 10) selected)
    | exact False.elim ((by decide +kernel : (46 : Source.BaseField) ≠ 10) selected)
    | exact False.elim ((by decide +kernel : (0 : Source.BaseField) ≠ 10) selected)

theorem tag26_region (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 8) = 26) :
    196608 ≤ row.val ∧ row.val < 204800 := by
  have rowBound : row.val < 8388608 := row.isLt
  rw [tag_value] at selected
  simp only [tagSegments, constantTagValue] at selected
  split_ifs at selected
  all_goals first
    | omega
    | exact False.elim ((by decide +kernel : (1 : Source.BaseField) ≠ 26) selected)
    | exact False.elim ((by decide +kernel : (10 : Source.BaseField) ≠ 26) selected)
    | exact False.elim ((by decide +kernel : (41 : Source.BaseField) ≠ 26) selected)
    | exact False.elim ((by decide +kernel : (46 : Source.BaseField) ≠ 26) selected)
    | exact False.elim ((by decide +kernel : (0 : Source.BaseField) ≠ 26) selected)

theorem tag41_region (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 8) = 41) :
    204800 ≤ row.val ∧ row.val < 270336 := by
  have rowBound : row.val < 8388608 := row.isLt
  rw [tag_value] at selected
  simp only [tagSegments, constantTagValue] at selected
  split_ifs at selected
  all_goals first
    | omega
    | exact False.elim ((by decide +kernel : (1 : Source.BaseField) ≠ 41) selected)
    | exact False.elim ((by decide +kernel : (10 : Source.BaseField) ≠ 41) selected)
    | exact False.elim ((by decide +kernel : (26 : Source.BaseField) ≠ 41) selected)
    | exact False.elim ((by decide +kernel : (46 : Source.BaseField) ≠ 41) selected)
    | exact False.elim ((by decide +kernel : (0 : Source.BaseField) ≠ 41) selected)

theorem tag46_region (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 8) = 46) :
    270336 ≤ row.val ∧ row.val < 1318912 := by
  have rowBound : row.val < 8388608 := row.isLt
  rw [tag_value] at selected
  simp only [tagSegments, constantTagValue] at selected
  split_ifs at selected
  all_goals first
    | omega
    | exact False.elim ((by decide +kernel : (1 : Source.BaseField) ≠ 46) selected)
    | exact False.elim ((by decide +kernel : (10 : Source.BaseField) ≠ 46) selected)
    | exact False.elim ((by decide +kernel : (26 : Source.BaseField) ≠ 46) selected)
    | exact False.elim ((by decide +kernel : (41 : Source.BaseField) ≠ 46) selected)
    | exact False.elim ((by decide +kernel : (0 : Source.BaseField) ≠ 46) selected)

theorem tag0_region (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 8) = 0) :
    1318912 ≤ row.val ∧ row.val < 8388608 := by
  have rowBound : row.val < 8388608 := row.isLt
  rw [tag_value] at selected
  simp only [tagSegments, constantTagValue] at selected
  split_ifs at selected
  all_goals first
    | omega
    | exact False.elim ((by decide +kernel : (1 : Source.BaseField) ≠ 0) selected)
    | exact False.elim ((by decide +kernel : (10 : Source.BaseField) ≠ 0) selected)
    | exact False.elim ((by decide +kernel : (26 : Source.BaseField) ≠ 0) selected)
    | exact False.elim ((by decide +kernel : (41 : Source.BaseField) ≠ 0) selected)
    | exact False.elim ((by decide +kernel : (46 : Source.BaseField) ≠ 0) selected)

end Airbender.Compiler.FixedSetupNative.MulDiv
