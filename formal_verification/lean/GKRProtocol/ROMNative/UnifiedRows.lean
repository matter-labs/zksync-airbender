import GKRProtocol.UnifiedRegionColumns.Column0
import GKRProtocol.UnifiedRegionColumns.Column1
import GKRProtocol.UnifiedRegionColumns.Column2
import GKRProtocol.UnifiedRegionColumns.Column3
import GKRProtocol.UnifiedRegionColumns.Column4
import GKRProtocol.UnifiedRegionColumns.Column5
import GKRProtocol.UnifiedRegionColumns.Column6
import GKRProtocol.UnifiedRegionColumns.Column7
import GKRProtocol.UnifiedRegionColumns.Column8
import GKRProtocol.UnifiedRegionColumns.Column9
import GKRProtocol.MaterializedNative.UnifiedUncached
import GKRProtocol.UnifiedLogicalRegions

namespace Airbender.Compiler.ROMNative.UnifiedRows
open Airbender Airbender.Compiler Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model

def nativeRow (row : Fin 8388608) : Vector Source.BaseField 10 := (nativeSetup.imported.data.row row).map (fun n : Int => (n : Source.BaseField))

theorem region0_column (column : Fin 10) (index : Fin 1) :
    nativeSetup.imported.data.columns[column.val].get? (0 + index.val) = UnifiedReduced.Setup.nativeZeroData.columns[column.val].get? index.val := by
  fin_cases column
  · exact UnifiedRegionColumns.Column0.region_value0 index
  · exact UnifiedRegionColumns.Column1.region_value0 index
  · exact UnifiedRegionColumns.Column2.region_value0 index
  · exact UnifiedRegionColumns.Column3.region_value0 index
  · exact UnifiedRegionColumns.Column4.region_value0 index
  · exact UnifiedRegionColumns.Column5.region_value0 index
  · exact UnifiedRegionColumns.Column6.region_value0 index
  · exact UnifiedRegionColumns.Column7.region_value0 index
  · exact UnifiedRegionColumns.Column8.region_value0 index
  · exact UnifiedRegionColumns.Column9.region_value0 index

theorem region0_row (index : Fin 1) :
    nativeRow ⟨0 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.nativeZeroData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  have same := region0_column ⟨column, bound⟩ index
  simp only [Nat.zero_add] at same
  rw [same]

theorem region0_retained (index : Fin 1) :
    nativeRow ⟨0 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.importedRow ⟨0 + index.val, by have := index.isLt; omega⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  rw [region0_row]
  rw [UnifiedLogicalRegions.region0_row]
  rfl

theorem region1_column (column : Fin 10) (index : Fin 131072) :
    nativeSetup.imported.data.columns[column.val].get? (1 + index.val) = UnifiedReduced.Setup.nativeRegisterZeroData.columns[column.val].get? index.val := by
  fin_cases column
  · exact UnifiedRegionColumns.Column0.region_value1 index
  · exact UnifiedRegionColumns.Column1.region_value1 index
  · exact UnifiedRegionColumns.Column2.region_value1 index
  · exact UnifiedRegionColumns.Column3.region_value1 index
  · exact UnifiedRegionColumns.Column4.region_value1 index
  · exact UnifiedRegionColumns.Column5.region_value1 index
  · exact UnifiedRegionColumns.Column6.region_value1 index
  · exact UnifiedRegionColumns.Column7.region_value1 index
  · exact UnifiedRegionColumns.Column8.region_value1 index
  · exact UnifiedRegionColumns.Column9.region_value1 index

theorem region1_row (index : Fin 131072) :
    nativeRow ⟨1 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.nativeRegisterZeroData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region1_column ⟨column, bound⟩ index]

theorem region1_retained (index : Fin 131072) :
    nativeRow ⟨1 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.importedRow ⟨524545 + index.val, by have := index.isLt; omega⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  rw [region1_row]
  rw [UnifiedLogicalRegions.region7_row]
  rfl

theorem region2_column (column : Fin 10) (index : Fin 65536) :
    nativeSetup.imported.data.columns[column.val].get? (131073 + index.val) = UnifiedReduced.Setup.nativeCleanupData.columns[column.val].get? index.val := by
  fin_cases column
  · exact UnifiedRegionColumns.Column0.region_value2 index
  · exact UnifiedRegionColumns.Column1.region_value2 index
  · exact UnifiedRegionColumns.Column2.region_value2 index
  · exact UnifiedRegionColumns.Column3.region_value2 index
  · exact UnifiedRegionColumns.Column4.region_value2 index
  · exact UnifiedRegionColumns.Column5.region_value2 index
  · exact UnifiedRegionColumns.Column6.region_value2 index
  · exact UnifiedRegionColumns.Column7.region_value2 index
  · exact UnifiedRegionColumns.Column8.region_value2 index
  · exact UnifiedRegionColumns.Column9.region_value2 index

theorem region2_row (index : Fin 65536) :
    nativeRow ⟨131073 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.nativeCleanupData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region2_column ⟨column, bound⟩ index]

theorem region2_retained (index : Fin 65536) :
    nativeRow ⟨131073 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.importedRow ⟨721153 + index.val, by have := index.isLt; omega⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  rw [region2_row]
  rw [UnifiedLogicalRegions.region9_row]
  rfl

theorem region3_column (column : Fin 10) (index : Fin 256) :
    nativeSetup.imported.data.columns[column.val].get? (196609 + index.val) = UnifiedReduced.Setup.nativeByteSignData.columns[column.val].get? index.val := by
  fin_cases column
  · exact UnifiedRegionColumns.Column0.region_value3 index
  · exact UnifiedRegionColumns.Column1.region_value3 index
  · exact UnifiedRegionColumns.Column2.region_value3 index
  · exact UnifiedRegionColumns.Column3.region_value3 index
  · exact UnifiedRegionColumns.Column4.region_value3 index
  · exact UnifiedRegionColumns.Column5.region_value3 index
  · exact UnifiedRegionColumns.Column6.region_value3 index
  · exact UnifiedRegionColumns.Column7.region_value3 index
  · exact UnifiedRegionColumns.Column8.region_value3 index
  · exact UnifiedRegionColumns.Column9.region_value3 index

theorem region3_row (index : Fin 256) :
    nativeRow ⟨196609 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.nativeByteSignData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region3_column ⟨column, bound⟩ index]

theorem region3_retained (index : Fin 256) :
    nativeRow ⟨196609 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.importedRow ⟨1 + index.val, by have := index.isLt; omega⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  rw [region3_row]
  rw [UnifiedLogicalRegions.region1_row]
  rfl

theorem region4_column (column : Fin 10) (index : Fin 65536) :
    nativeSetup.imported.data.columns[column.val].get? (196865 + index.val) = UnifiedReduced.Setup.nativeSignData.columns[column.val].get? index.val := by
  fin_cases column
  · exact UnifiedRegionColumns.Column0.region_value4 index
  · exact UnifiedRegionColumns.Column1.region_value4 index
  · exact UnifiedRegionColumns.Column2.region_value4 index
  · exact UnifiedRegionColumns.Column3.region_value4 index
  · exact UnifiedRegionColumns.Column4.region_value4 index
  · exact UnifiedRegionColumns.Column5.region_value4 index
  · exact UnifiedRegionColumns.Column6.region_value4 index
  · exact UnifiedRegionColumns.Column7.region_value4 index
  · exact UnifiedRegionColumns.Column8.region_value4 index
  · exact UnifiedRegionColumns.Column9.region_value4 index

theorem region4_row (index : Fin 65536) :
    nativeRow ⟨196865 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.nativeSignData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region4_column ⟨column, bound⟩ index]

theorem region4_retained (index : Fin 65536) :
    nativeRow ⟨196865 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.importedRow ⟨655617 + index.val, by have := index.isLt; omega⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  rw [region4_row]
  rw [UnifiedLogicalRegions.region8_row]
  rfl

theorem region5_column (column : Fin 10) (index : Fin 65536) :
    nativeSetup.imported.data.columns[column.val].get? (262401 + index.val) = UnifiedReduced.Setup.nativeTruncationData.columns[column.val].get? index.val := by
  fin_cases column
  · exact UnifiedRegionColumns.Column0.region_value5 index
  · exact UnifiedRegionColumns.Column1.region_value5 index
  · exact UnifiedRegionColumns.Column2.region_value5 index
  · exact UnifiedRegionColumns.Column3.region_value5 index
  · exact UnifiedRegionColumns.Column4.region_value5 index
  · exact UnifiedRegionColumns.Column5.region_value5 index
  · exact UnifiedRegionColumns.Column6.region_value5 index
  · exact UnifiedRegionColumns.Column7.region_value5 index
  · exact UnifiedRegionColumns.Column8.region_value5 index
  · exact UnifiedRegionColumns.Column9.region_value5 index

theorem region5_row (index : Fin 65536) :
    nativeRow ⟨262401 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.nativeTruncationData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region5_column ⟨column, bound⟩ index]

theorem region5_retained (index : Fin 65536) :
    nativeRow ⟨262401 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.importedRow ⟨196865 + index.val, by have := index.isLt; omega⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  rw [region5_row]
  rw [UnifiedLogicalRegions.region5_row]
  rfl

theorem region6_column (column : Fin 10) (index : Fin 262144) :
    nativeSetup.imported.data.columns[column.val].get? (327937 + index.val) = UnifiedReduced.Setup.nativeShiftData.columns[column.val].get? index.val := by
  fin_cases column
  · exact UnifiedRegionColumns.Column0.region_value6 index
  · exact UnifiedRegionColumns.Column1.region_value6 index
  · exact UnifiedRegionColumns.Column2.region_value6 index
  · exact UnifiedRegionColumns.Column3.region_value6 index
  · exact UnifiedRegionColumns.Column4.region_value6 index
  · exact UnifiedRegionColumns.Column5.region_value6 index
  · exact UnifiedRegionColumns.Column6.region_value6 index
  · exact UnifiedRegionColumns.Column7.region_value6 index
  · exact UnifiedRegionColumns.Column8.region_value6 index
  · exact UnifiedRegionColumns.Column9.region_value6 index

theorem region6_row (index : Fin 262144) :
    nativeRow ⟨327937 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.nativeShiftData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region6_column ⟨column, bound⟩ index]

theorem region6_retained (index : Fin 262144) :
    nativeRow ⟨327937 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.importedRow ⟨262401 + index.val, by have := index.isLt; omega⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  rw [region6_row]
  rw [UnifiedLogicalRegions.region6_row]
  rfl

theorem region7_column (column : Fin 10) (index : Fin 1048576) :
    nativeSetup.imported.data.columns[column.val].get? (590081 + index.val) = UnifiedReduced.Setup.nativeROMData.columns[column.val].get? index.val := by
  fin_cases column
  · exact UnifiedRegionColumns.Column0.region_value7 index
  · exact UnifiedRegionColumns.Column1.region_value7 index
  · exact UnifiedRegionColumns.Column2.region_value7 index
  · exact UnifiedRegionColumns.Column3.region_value7 index
  · exact UnifiedRegionColumns.Column4.region_value7 index
  · exact UnifiedRegionColumns.Column5.region_value7 index
  · exact UnifiedRegionColumns.Column6.region_value7 index
  · exact UnifiedRegionColumns.Column7.region_value7 index
  · exact UnifiedRegionColumns.Column8.region_value7 index
  · exact UnifiedRegionColumns.Column9.region_value7 index

theorem region7_row (index : Fin 1048576) :
    nativeRow ⟨590081 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.nativeROMData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region7_column ⟨column, bound⟩ index]

theorem region7_retained (index : Fin 1048576) :
    nativeRow ⟨590081 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.importedRow ⟨1048961 + index.val, by have := index.isLt; omega⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  rw [region7_row]
  simp only [UnifiedReduced.Setup.importedRow, dif_neg (by have := index.isLt; omega : ¬1048961 + index.val < 1048961), Nat.add_sub_cancel_left]

theorem region8_column (column : Fin 10) (index : Fin 65536) :
    nativeSetup.imported.data.columns[column.val].get? (1638657 + index.val) = UnifiedReduced.Setup.nativeRotate16Data.columns[column.val].get? index.val := by
  fin_cases column
  · exact UnifiedRegionColumns.Column0.region_value8 index
  · exact UnifiedRegionColumns.Column1.region_value8 index
  · exact UnifiedRegionColumns.Column2.region_value8 index
  · exact UnifiedRegionColumns.Column3.region_value8 index
  · exact UnifiedRegionColumns.Column4.region_value8 index
  · exact UnifiedRegionColumns.Column5.region_value8 index
  · exact UnifiedRegionColumns.Column6.region_value8 index
  · exact UnifiedRegionColumns.Column7.region_value8 index
  · exact UnifiedRegionColumns.Column8.region_value8 index
  · exact UnifiedRegionColumns.Column9.region_value8 index

theorem region8_row (index : Fin 65536) :
    nativeRow ⟨1638657 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.nativeRotate16Data.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region8_column ⟨column, bound⟩ index]

theorem region8_retained (index : Fin 65536) :
    nativeRow ⟨1638657 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.importedRow ⟨786817 + index.val, by have := index.isLt; omega⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  rw [region8_row]
  rw [UnifiedLogicalRegions.region11_row]
  rfl

theorem region9_column (column : Fin 10) (index : Fin 65536) :
    nativeSetup.imported.data.columns[column.val].get? (1704193 + index.val) = UnifiedReduced.Setup.nativeRotate12Data.columns[column.val].get? index.val := by
  fin_cases column
  · exact UnifiedRegionColumns.Column0.region_value9 index
  · exact UnifiedRegionColumns.Column1.region_value9 index
  · exact UnifiedRegionColumns.Column2.region_value9 index
  · exact UnifiedRegionColumns.Column3.region_value9 index
  · exact UnifiedRegionColumns.Column4.region_value9 index
  · exact UnifiedRegionColumns.Column5.region_value9 index
  · exact UnifiedRegionColumns.Column6.region_value9 index
  · exact UnifiedRegionColumns.Column7.region_value9 index
  · exact UnifiedRegionColumns.Column8.region_value9 index
  · exact UnifiedRegionColumns.Column9.region_value9 index

theorem region9_row (index : Fin 65536) :
    nativeRow ⟨1704193 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.nativeRotate12Data.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region9_column ⟨column, bound⟩ index]

theorem region9_retained (index : Fin 65536) :
    nativeRow ⟨1704193 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.importedRow ⟨852353 + index.val, by have := index.isLt; omega⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  rw [region9_row]
  rw [UnifiedLogicalRegions.region12_row]
  rfl

theorem region10_column (column : Fin 10) (index : Fin 65536) :
    nativeSetup.imported.data.columns[column.val].get? (1769729 + index.val) = UnifiedReduced.Setup.nativeRotate8Data.columns[column.val].get? index.val := by
  fin_cases column
  · exact UnifiedRegionColumns.Column0.region_value10 index
  · exact UnifiedRegionColumns.Column1.region_value10 index
  · exact UnifiedRegionColumns.Column2.region_value10 index
  · exact UnifiedRegionColumns.Column3.region_value10 index
  · exact UnifiedRegionColumns.Column4.region_value10 index
  · exact UnifiedRegionColumns.Column5.region_value10 index
  · exact UnifiedRegionColumns.Column6.region_value10 index
  · exact UnifiedRegionColumns.Column7.region_value10 index
  · exact UnifiedRegionColumns.Column8.region_value10 index
  · exact UnifiedRegionColumns.Column9.region_value10 index

theorem region10_row (index : Fin 65536) :
    nativeRow ⟨1769729 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.nativeRotate8Data.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region10_column ⟨column, bound⟩ index]

theorem region10_retained (index : Fin 65536) :
    nativeRow ⟨1769729 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.importedRow ⟨917889 + index.val, by have := index.isLt; omega⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  rw [region10_row]
  rw [UnifiedLogicalRegions.region13_row]
  rfl

theorem region11_column (column : Fin 10) (index : Fin 65536) :
    nativeSetup.imported.data.columns[column.val].get? (1835265 + index.val) = UnifiedReduced.Setup.nativeRotate7Data.columns[column.val].get? index.val := by
  fin_cases column
  · exact UnifiedRegionColumns.Column0.region_value11 index
  · exact UnifiedRegionColumns.Column1.region_value11 index
  · exact UnifiedRegionColumns.Column2.region_value11 index
  · exact UnifiedRegionColumns.Column3.region_value11 index
  · exact UnifiedRegionColumns.Column4.region_value11 index
  · exact UnifiedRegionColumns.Column5.region_value11 index
  · exact UnifiedRegionColumns.Column6.region_value11 index
  · exact UnifiedRegionColumns.Column7.region_value11 index
  · exact UnifiedRegionColumns.Column8.region_value11 index
  · exact UnifiedRegionColumns.Column9.region_value11 index

theorem region11_row (index : Fin 65536) :
    nativeRow ⟨1835265 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.nativeRotate7Data.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region11_column ⟨column, bound⟩ index]

theorem region11_retained (index : Fin 65536) :
    nativeRow ⟨1835265 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.importedRow ⟨983425 + index.val, by have := index.isLt; omega⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  rw [region11_row]
  rw [UnifiedLogicalRegions.region14_row]
  rfl

theorem region12_column (column : Fin 10) (index : Fin 128) :
    nativeSetup.imported.data.columns[column.val].get? (1900801 + index.val) = UnifiedReduced.Setup.nativeConditionalData.columns[column.val].get? index.val := by
  fin_cases column
  · exact UnifiedRegionColumns.Column0.region_value12 index
  · exact UnifiedRegionColumns.Column1.region_value12 index
  · exact UnifiedRegionColumns.Column2.region_value12 index
  · exact UnifiedRegionColumns.Column3.region_value12 index
  · exact UnifiedRegionColumns.Column4.region_value12 index
  · exact UnifiedRegionColumns.Column5.region_value12 index
  · exact UnifiedRegionColumns.Column6.region_value12 index
  · exact UnifiedRegionColumns.Column7.region_value12 index
  · exact UnifiedRegionColumns.Column8.region_value12 index
  · exact UnifiedRegionColumns.Column9.region_value12 index

theorem region12_row (index : Fin 128) :
    nativeRow ⟨1900801 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.nativeConditionalData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region12_column ⟨column, bound⟩ index]

theorem region12_retained (index : Fin 128) :
    nativeRow ⟨1900801 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.importedRow ⟨786689 + index.val, by have := index.isLt; omega⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  rw [region12_row]
  rw [UnifiedLogicalRegions.region10_row]
  rfl

theorem region13_column (column : Fin 10) (index : Fin 65536) :
    nativeSetup.imported.data.columns[column.val].get? (1900929 + index.val) = UnifiedReduced.Setup.nativeXorData.columns[column.val].get? index.val := by
  fin_cases column
  · exact UnifiedRegionColumns.Column0.region_value13 index
  · exact UnifiedRegionColumns.Column1.region_value13 index
  · exact UnifiedRegionColumns.Column2.region_value13 index
  · exact UnifiedRegionColumns.Column3.region_value13 index
  · exact UnifiedRegionColumns.Column4.region_value13 index
  · exact UnifiedRegionColumns.Column5.region_value13 index
  · exact UnifiedRegionColumns.Column6.region_value13 index
  · exact UnifiedRegionColumns.Column7.region_value13 index
  · exact UnifiedRegionColumns.Column8.region_value13 index
  · exact UnifiedRegionColumns.Column9.region_value13 index

theorem region13_row (index : Fin 65536) :
    nativeRow ⟨1900929 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.nativeXorData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region13_column ⟨column, bound⟩ index]

theorem region13_retained (index : Fin 65536) :
    nativeRow ⟨1900929 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.importedRow ⟨257 + index.val, by have := index.isLt; omega⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  rw [region13_row]
  rw [UnifiedLogicalRegions.region2_row]
  rfl

theorem region14_column (column : Fin 10) (index : Fin 65536) :
    nativeSetup.imported.data.columns[column.val].get? (1966465 + index.val) = UnifiedReduced.Setup.nativeOrData.columns[column.val].get? index.val := by
  fin_cases column
  · exact UnifiedRegionColumns.Column0.region_value14 index
  · exact UnifiedRegionColumns.Column1.region_value14 index
  · exact UnifiedRegionColumns.Column2.region_value14 index
  · exact UnifiedRegionColumns.Column3.region_value14 index
  · exact UnifiedRegionColumns.Column4.region_value14 index
  · exact UnifiedRegionColumns.Column5.region_value14 index
  · exact UnifiedRegionColumns.Column6.region_value14 index
  · exact UnifiedRegionColumns.Column7.region_value14 index
  · exact UnifiedRegionColumns.Column8.region_value14 index
  · exact UnifiedRegionColumns.Column9.region_value14 index

theorem region14_row (index : Fin 65536) :
    nativeRow ⟨1966465 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.nativeOrData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region14_column ⟨column, bound⟩ index]

theorem region14_retained (index : Fin 65536) :
    nativeRow ⟨1966465 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.importedRow ⟨65793 + index.val, by have := index.isLt; omega⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  rw [region14_row]
  rw [UnifiedLogicalRegions.region3_row]
  rfl

theorem region15_column (column : Fin 10) (index : Fin 65536) :
    nativeSetup.imported.data.columns[column.val].get? (2032001 + index.val) = UnifiedReduced.Setup.nativeAndData.columns[column.val].get? index.val := by
  fin_cases column
  · exact UnifiedRegionColumns.Column0.region_value15 index
  · exact UnifiedRegionColumns.Column1.region_value15 index
  · exact UnifiedRegionColumns.Column2.region_value15 index
  · exact UnifiedRegionColumns.Column3.region_value15 index
  · exact UnifiedRegionColumns.Column4.region_value15 index
  · exact UnifiedRegionColumns.Column5.region_value15 index
  · exact UnifiedRegionColumns.Column6.region_value15 index
  · exact UnifiedRegionColumns.Column7.region_value15 index
  · exact UnifiedRegionColumns.Column8.region_value15 index
  · exact UnifiedRegionColumns.Column9.region_value15 index

theorem region15_row (index : Fin 65536) :
    nativeRow ⟨2032001 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.nativeAndData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region15_column ⟨column, bound⟩ index]

theorem region15_retained (index : Fin 65536) :
    nativeRow ⟨2032001 + index.val, by have := index.isLt; omega⟩ =
      (UnifiedReduced.Setup.importedRow ⟨131329 + index.val, by have := index.isLt; omega⟩).map (fun n : Nat => (n : Source.BaseField)) := by
  rw [region15_row]
  rw [UnifiedLogicalRegions.region4_row]
  rfl

theorem prefix_member (index : Fin 2097537) :
    (UnifiedReduced.Setup.importedTable (p := babyBearModulus)).Contains #[] (nativeRow ⟨index.val, by have := index.isLt; omega⟩) := by
  by_cases selected0 : index.val < 1
  ·
    let localIndex : Fin 1 := ⟨index.val - 0, by have := index.isLt; omega⟩
    have actual := region0_retained localIndex
    have position : 0 + localIndex.val = index.val := by dsimp [localIndex]; omega
    have same : nativeRow ⟨0 + localIndex.val, by have := localIndex.isLt; omega⟩ = nativeRow ⟨index.val, by have := index.isLt; omega⟩ := congrArg nativeRow (Fin.ext position)
    exact ⟨⟨0 + localIndex.val, by change 0 + localIndex.val < 2097537; have := localIndex.isLt; omega⟩, same.symm.trans actual⟩
  ·
    by_cases selected1 : index.val < 131073
    ·
      let localIndex : Fin 131072 := ⟨index.val - 1, by have := index.isLt; omega⟩
      have actual := region1_retained localIndex
      have position : 1 + localIndex.val = index.val := by dsimp [localIndex]; omega
      have same : nativeRow ⟨1 + localIndex.val, by have := localIndex.isLt; omega⟩ = nativeRow ⟨index.val, by have := index.isLt; omega⟩ := congrArg nativeRow (Fin.ext position)
      exact ⟨⟨524545 + localIndex.val, by change 524545 + localIndex.val < 2097537; have := localIndex.isLt; omega⟩, same.symm.trans actual⟩
    ·
      by_cases selected2 : index.val < 196609
      ·
        let localIndex : Fin 65536 := ⟨index.val - 131073, by have := index.isLt; omega⟩
        have actual := region2_retained localIndex
        have position : 131073 + localIndex.val = index.val := by dsimp [localIndex]; omega
        have same : nativeRow ⟨131073 + localIndex.val, by have := localIndex.isLt; omega⟩ = nativeRow ⟨index.val, by have := index.isLt; omega⟩ := congrArg nativeRow (Fin.ext position)
        exact ⟨⟨721153 + localIndex.val, by change 721153 + localIndex.val < 2097537; have := localIndex.isLt; omega⟩, same.symm.trans actual⟩
      ·
        by_cases selected3 : index.val < 196865
        ·
          let localIndex : Fin 256 := ⟨index.val - 196609, by have := index.isLt; omega⟩
          have actual := region3_retained localIndex
          have position : 196609 + localIndex.val = index.val := by dsimp [localIndex]; omega
          have same : nativeRow ⟨196609 + localIndex.val, by have := localIndex.isLt; omega⟩ = nativeRow ⟨index.val, by have := index.isLt; omega⟩ := congrArg nativeRow (Fin.ext position)
          exact ⟨⟨1 + localIndex.val, by change 1 + localIndex.val < 2097537; have := localIndex.isLt; omega⟩, same.symm.trans actual⟩
        ·
          by_cases selected4 : index.val < 262401
          ·
            let localIndex : Fin 65536 := ⟨index.val - 196865, by have := index.isLt; omega⟩
            have actual := region4_retained localIndex
            have position : 196865 + localIndex.val = index.val := by dsimp [localIndex]; omega
            have same : nativeRow ⟨196865 + localIndex.val, by have := localIndex.isLt; omega⟩ = nativeRow ⟨index.val, by have := index.isLt; omega⟩ := congrArg nativeRow (Fin.ext position)
            exact ⟨⟨655617 + localIndex.val, by change 655617 + localIndex.val < 2097537; have := localIndex.isLt; omega⟩, same.symm.trans actual⟩
          ·
            by_cases selected5 : index.val < 327937
            ·
              let localIndex : Fin 65536 := ⟨index.val - 262401, by have := index.isLt; omega⟩
              have actual := region5_retained localIndex
              have position : 262401 + localIndex.val = index.val := by dsimp [localIndex]; omega
              have same : nativeRow ⟨262401 + localIndex.val, by have := localIndex.isLt; omega⟩ = nativeRow ⟨index.val, by have := index.isLt; omega⟩ := congrArg nativeRow (Fin.ext position)
              exact ⟨⟨196865 + localIndex.val, by change 196865 + localIndex.val < 2097537; have := localIndex.isLt; omega⟩, same.symm.trans actual⟩
            ·
              by_cases selected6 : index.val < 590081
              ·
                let localIndex : Fin 262144 := ⟨index.val - 327937, by have := index.isLt; omega⟩
                have actual := region6_retained localIndex
                have position : 327937 + localIndex.val = index.val := by dsimp [localIndex]; omega
                have same : nativeRow ⟨327937 + localIndex.val, by have := localIndex.isLt; omega⟩ = nativeRow ⟨index.val, by have := index.isLt; omega⟩ := congrArg nativeRow (Fin.ext position)
                exact ⟨⟨262401 + localIndex.val, by change 262401 + localIndex.val < 2097537; have := localIndex.isLt; omega⟩, same.symm.trans actual⟩
              ·
                by_cases selected7 : index.val < 1638657
                ·
                  let localIndex : Fin 1048576 := ⟨index.val - 590081, by have := index.isLt; omega⟩
                  have actual := region7_retained localIndex
                  have position : 590081 + localIndex.val = index.val := by dsimp [localIndex]; omega
                  have same : nativeRow ⟨590081 + localIndex.val, by have := localIndex.isLt; omega⟩ = nativeRow ⟨index.val, by have := index.isLt; omega⟩ := congrArg nativeRow (Fin.ext position)
                  exact ⟨⟨1048961 + localIndex.val, by change 1048961 + localIndex.val < 2097537; have := localIndex.isLt; omega⟩, same.symm.trans actual⟩
                ·
                  by_cases selected8 : index.val < 1704193
                  ·
                    let localIndex : Fin 65536 := ⟨index.val - 1638657, by have := index.isLt; omega⟩
                    have actual := region8_retained localIndex
                    have position : 1638657 + localIndex.val = index.val := by dsimp [localIndex]; omega
                    have same : nativeRow ⟨1638657 + localIndex.val, by have := localIndex.isLt; omega⟩ = nativeRow ⟨index.val, by have := index.isLt; omega⟩ := congrArg nativeRow (Fin.ext position)
                    exact ⟨⟨786817 + localIndex.val, by change 786817 + localIndex.val < 2097537; have := localIndex.isLt; omega⟩, same.symm.trans actual⟩
                  ·
                    by_cases selected9 : index.val < 1769729
                    ·
                      let localIndex : Fin 65536 := ⟨index.val - 1704193, by have := index.isLt; omega⟩
                      have actual := region9_retained localIndex
                      have position : 1704193 + localIndex.val = index.val := by dsimp [localIndex]; omega
                      have same : nativeRow ⟨1704193 + localIndex.val, by have := localIndex.isLt; omega⟩ = nativeRow ⟨index.val, by have := index.isLt; omega⟩ := congrArg nativeRow (Fin.ext position)
                      exact ⟨⟨852353 + localIndex.val, by change 852353 + localIndex.val < 2097537; have := localIndex.isLt; omega⟩, same.symm.trans actual⟩
                    ·
                      by_cases selected10 : index.val < 1835265
                      ·
                        let localIndex : Fin 65536 := ⟨index.val - 1769729, by have := index.isLt; omega⟩
                        have actual := region10_retained localIndex
                        have position : 1769729 + localIndex.val = index.val := by dsimp [localIndex]; omega
                        have same : nativeRow ⟨1769729 + localIndex.val, by have := localIndex.isLt; omega⟩ = nativeRow ⟨index.val, by have := index.isLt; omega⟩ := congrArg nativeRow (Fin.ext position)
                        exact ⟨⟨917889 + localIndex.val, by change 917889 + localIndex.val < 2097537; have := localIndex.isLt; omega⟩, same.symm.trans actual⟩
                      ·
                        by_cases selected11 : index.val < 1900801
                        ·
                          let localIndex : Fin 65536 := ⟨index.val - 1835265, by have := index.isLt; omega⟩
                          have actual := region11_retained localIndex
                          have position : 1835265 + localIndex.val = index.val := by dsimp [localIndex]; omega
                          have same : nativeRow ⟨1835265 + localIndex.val, by have := localIndex.isLt; omega⟩ = nativeRow ⟨index.val, by have := index.isLt; omega⟩ := congrArg nativeRow (Fin.ext position)
                          exact ⟨⟨983425 + localIndex.val, by change 983425 + localIndex.val < 2097537; have := localIndex.isLt; omega⟩, same.symm.trans actual⟩
                        ·
                          by_cases selected12 : index.val < 1900929
                          ·
                            let localIndex : Fin 128 := ⟨index.val - 1900801, by have := index.isLt; omega⟩
                            have actual := region12_retained localIndex
                            have position : 1900801 + localIndex.val = index.val := by dsimp [localIndex]; omega
                            have same : nativeRow ⟨1900801 + localIndex.val, by have := localIndex.isLt; omega⟩ = nativeRow ⟨index.val, by have := index.isLt; omega⟩ := congrArg nativeRow (Fin.ext position)
                            exact ⟨⟨786689 + localIndex.val, by change 786689 + localIndex.val < 2097537; have := localIndex.isLt; omega⟩, same.symm.trans actual⟩
                          ·
                            by_cases selected13 : index.val < 1966465
                            ·
                              let localIndex : Fin 65536 := ⟨index.val - 1900929, by have := index.isLt; omega⟩
                              have actual := region13_retained localIndex
                              have position : 1900929 + localIndex.val = index.val := by dsimp [localIndex]; omega
                              have same : nativeRow ⟨1900929 + localIndex.val, by have := localIndex.isLt; omega⟩ = nativeRow ⟨index.val, by have := index.isLt; omega⟩ := congrArg nativeRow (Fin.ext position)
                              exact ⟨⟨257 + localIndex.val, by change 257 + localIndex.val < 2097537; have := localIndex.isLt; omega⟩, same.symm.trans actual⟩
                            ·
                              by_cases selected14 : index.val < 2032001
                              ·
                                let localIndex : Fin 65536 := ⟨index.val - 1966465, by have := index.isLt; omega⟩
                                have actual := region14_retained localIndex
                                have position : 1966465 + localIndex.val = index.val := by dsimp [localIndex]; omega
                                have same : nativeRow ⟨1966465 + localIndex.val, by have := localIndex.isLt; omega⟩ = nativeRow ⟨index.val, by have := index.isLt; omega⟩ := congrArg nativeRow (Fin.ext position)
                                exact ⟨⟨65793 + localIndex.val, by change 65793 + localIndex.val < 2097537; have := localIndex.isLt; omega⟩, same.symm.trans actual⟩
                              ·
                                let localIndex : Fin 65536 := ⟨index.val - 2032001, by have := index.isLt; omega⟩
                                have actual := region15_retained localIndex
                                have position : 2032001 + localIndex.val = index.val := by dsimp [localIndex]; omega
                                have same : nativeRow ⟨2032001 + localIndex.val, by have := localIndex.isLt; omega⟩ = nativeRow ⟨index.val, by have := index.isLt; omega⟩ := congrArg nativeRow (Fin.ext position)
                                exact ⟨⟨131329 + localIndex.val, by change 131329 + localIndex.val < 2097537; have := localIndex.isLt; omega⟩, same.symm.trans actual⟩

end Airbender.Compiler.ROMNative.UnifiedRows
