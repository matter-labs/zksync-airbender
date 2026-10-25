import GKRProtocol.SubwordPrefixNative.Column0
import GKRProtocol.SubwordPrefixNative.Column1
import GKRProtocol.SubwordPrefixNative.Column2
import GKRProtocol.SubwordPrefixNative.Column3
import GKRProtocol.SubwordPrefixNative.Column4
import GKRProtocol.SubwordPrefixNative.Column5
import GKRProtocol.SubwordPrefixNative.Column6
import GKRProtocol.SubwordPrefixNative.Column7
import GKRProtocol.SubwordPrefixNative.Column8
import GKRProtocol.MaterializedNative.SubwordMemoryUncached

namespace Airbender.Compiler.ROMNative.SubwordRows
open Airbender Airbender.Compiler Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model

def nativeRow (row : Fin 16777216) : Vector Source.BaseField 9 := (nativeSetup.imported.data.row row).map (fun n : Int => (n : Source.BaseField))

theorem region0_column (column : Fin 9) (index : Fin 1) :
    nativeSetup.imported.data.columns[column.val].get? (0 + index.val) = Verification.subwordZeroData.columns[column.val].get? index.val := by
  fin_cases column
  · exact SubwordPrefixNative.Column0.region_value0 index
  · exact SubwordPrefixNative.Column1.region_value0 index
  · exact SubwordPrefixNative.Column2.region_value0 index
  · exact SubwordPrefixNative.Column3.region_value0 index
  · exact SubwordPrefixNative.Column4.region_value0 index
  · exact SubwordPrefixNative.Column5.region_value0 index
  · exact SubwordPrefixNative.Column6.region_value0 index
  · exact SubwordPrefixNative.Column7.region_value0 index
  · exact SubwordPrefixNative.Column8.region_value0 index

theorem region0_row (index : Fin 1) :
    nativeRow ⟨0 + index.val, by have := index.isLt; omega⟩ =
      (Verification.subwordZeroData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  have same := region0_column ⟨column, bound⟩ index
  simp only [Nat.zero_add] at same
  rw [same]

theorem region1_column (column : Fin 9) (index : Fin 131072) :
    nativeSetup.imported.data.columns[column.val].get? (1 + index.val) = Verification.storePlaceData.columns[column.val].get? index.val := by
  fin_cases column
  · exact SubwordPrefixNative.Column0.region_value1 index
  · exact SubwordPrefixNative.Column1.region_value1 index
  · exact SubwordPrefixNative.Column2.region_value1 index
  · exact SubwordPrefixNative.Column3.region_value1 index
  · exact SubwordPrefixNative.Column4.region_value1 index
  · exact SubwordPrefixNative.Column5.region_value1 index
  · exact SubwordPrefixNative.Column6.region_value1 index
  · exact SubwordPrefixNative.Column7.region_value1 index
  · exact SubwordPrefixNative.Column8.region_value1 index

theorem region1_row (index : Fin 131072) :
    nativeRow ⟨1 + index.val, by have := index.isLt; omega⟩ =
      (Verification.storePlaceData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region1_column ⟨column, bound⟩ index]

theorem region2_column (column : Fin 9) (index : Fin 131072) :
    nativeSetup.imported.data.columns[column.val].get? (131073 + index.val) = Verification.storeClearData.columns[column.val].get? index.val := by
  fin_cases column
  · exact SubwordPrefixNative.Column0.region_value2 index
  · exact SubwordPrefixNative.Column1.region_value2 index
  · exact SubwordPrefixNative.Column2.region_value2 index
  · exact SubwordPrefixNative.Column3.region_value2 index
  · exact SubwordPrefixNative.Column4.region_value2 index
  · exact SubwordPrefixNative.Column5.region_value2 index
  · exact SubwordPrefixNative.Column6.region_value2 index
  · exact SubwordPrefixNative.Column7.region_value2 index
  · exact SubwordPrefixNative.Column8.region_value2 index

theorem region2_row (index : Fin 131072) :
    nativeRow ⟨131073 + index.val, by have := index.isLt; omega⟩ =
      (Verification.storeClearData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region2_column ⟨column, bound⟩ index]

theorem region3_column (column : Fin 9) (index : Fin 131072) :
    nativeSetup.imported.data.columns[column.val].get? (262145 + index.val) = Verification.loadHalfData.columns[column.val].get? index.val := by
  fin_cases column
  · exact SubwordPrefixNative.Column0.region_value3 index
  · exact SubwordPrefixNative.Column1.region_value3 index
  · exact SubwordPrefixNative.Column2.region_value3 index
  · exact SubwordPrefixNative.Column3.region_value3 index
  · exact SubwordPrefixNative.Column4.region_value3 index
  · exact SubwordPrefixNative.Column5.region_value3 index
  · exact SubwordPrefixNative.Column6.region_value3 index
  · exact SubwordPrefixNative.Column7.region_value3 index
  · exact SubwordPrefixNative.Column8.region_value3 index

theorem region3_row (index : Fin 131072) :
    nativeRow ⟨262145 + index.val, by have := index.isLt; omega⟩ =
      (Verification.loadHalfData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region3_column ⟨column, bound⟩ index]

theorem region4_column (column : Fin 9) (index : Fin 262144) :
    nativeSetup.imported.data.columns[column.val].get? (393217 + index.val) = Verification.loadByteData.columns[column.val].get? index.val := by
  fin_cases column
  · exact SubwordPrefixNative.Column0.region_value4 index
  · exact SubwordPrefixNative.Column1.region_value4 index
  · exact SubwordPrefixNative.Column2.region_value4 index
  · exact SubwordPrefixNative.Column3.region_value4 index
  · exact SubwordPrefixNative.Column4.region_value4 index
  · exact SubwordPrefixNative.Column5.region_value4 index
  · exact SubwordPrefixNative.Column6.region_value4 index
  · exact SubwordPrefixNative.Column7.region_value4 index
  · exact SubwordPrefixNative.Column8.region_value4 index

theorem region4_row (index : Fin 262144) :
    nativeRow ⟨393217 + index.val, by have := index.isLt; omega⟩ =
      (Verification.loadByteData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region4_column ⟨column, bound⟩ index]

theorem region5_column (column : Fin 9) (index : Fin 4194304) :
    nativeSetup.imported.data.columns[column.val].get? (655361 + index.val) = Verification.subwordROMHalfData.columns[column.val].get? index.val := by
  fin_cases column
  · exact SubwordPrefixNative.Column0.region_value5 index
  · exact SubwordPrefixNative.Column1.region_value5 index
  · exact SubwordPrefixNative.Column2.region_value5 index
  · exact SubwordPrefixNative.Column3.region_value5 index
  · exact SubwordPrefixNative.Column4.region_value5 index
  · exact SubwordPrefixNative.Column5.region_value5 index
  · exact SubwordPrefixNative.Column6.region_value5 index
  · exact SubwordPrefixNative.Column7.region_value5 index
  · exact SubwordPrefixNative.Column8.region_value5 index

theorem region5_row (index : Fin 4194304) :
    nativeRow ⟨655361 + index.val, by have := index.isLt; omega⟩ =
      (Verification.subwordROMHalfData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region5_column ⟨column, bound⟩ index]

theorem region6_column (column : Fin 9) (index : Fin 8388608) :
    nativeSetup.imported.data.columns[column.val].get? (4849665 + index.val) = Verification.subwordROMByteData.columns[column.val].get? index.val := by
  fin_cases column
  · exact SubwordPrefixNative.Column0.region_value6 index
  · exact SubwordPrefixNative.Column1.region_value6 index
  · exact SubwordPrefixNative.Column2.region_value6 index
  · exact SubwordPrefixNative.Column3.region_value6 index
  · exact SubwordPrefixNative.Column4.region_value6 index
  · exact SubwordPrefixNative.Column5.region_value6 index
  · exact SubwordPrefixNative.Column6.region_value6 index
  · exact SubwordPrefixNative.Column7.region_value6 index
  · exact SubwordPrefixNative.Column8.region_value6 index

theorem region6_row (index : Fin 8388608) :
    nativeRow ⟨4849665 + index.val, by have := index.isLt; omega⟩ =
      (Verification.subwordROMByteData.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [nativeRow, TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast]
  rw [region6_column ⟨column, bound⟩ index]

theorem prefix_row (index : Fin 13238273) :
    nativeRow ⟨index.val, by have := index.isLt; omega⟩ =
      (Verification.importedSubwordRow index).map (fun n : Nat => (n : Source.BaseField)) := by
  by_cases selected0 : index.val < 1
  ·
    have actual := region0_row ⟨index.val - 0, by have := index.isLt; omega⟩
    have position : 0 + (index.val - 0) = index.val := by omega
    simp only [position] at actual
    have view : Verification.importedSubwordRow index = Verification.subwordZeroData.columns.map (fun column => (column.get? (index.val - 0)).getD 0) := by
      have zero : index = ⟨0, by decide⟩ := by
        apply Fin.ext
        change index.val = 0
        omega
      rw [zero]
      rfl
    rw [view]
    exact actual
  ·
    by_cases selected1 : index.val < 131073
    ·
      have actual := region1_row ⟨index.val - 1, by have := index.isLt; omega⟩
      have position : 1 + (index.val - 1) = index.val := by omega
      simp only [position] at actual
      have view : Verification.importedSubwordRow index = Verification.storePlaceData.columns.map (fun column => (column.get? (index.val - 1)).getD 0) := by
        unfold Verification.importedSubwordRow
        rw [if_pos (by change index.val < 655361; omega)]
        unfold Verification.subwordNativeRow
        rw [if_neg (by change index.val ≠ 0; omega)]
        rw [if_pos (by change index.val < 131073; omega)]
        rfl
      rw [view]
      exact actual
    ·
      by_cases selected2 : index.val < 262145
      ·
        have actual := region2_row ⟨index.val - 131073, by have := index.isLt; omega⟩
        have position : 131073 + (index.val - 131073) = index.val := by omega
        simp only [position] at actual
        have view : Verification.importedSubwordRow index = Verification.storeClearData.columns.map (fun column => (column.get? (index.val - 131073)).getD 0) := by
          unfold Verification.importedSubwordRow
          rw [if_pos (by change index.val < 655361; omega)]
          unfold Verification.subwordNativeRow
          rw [if_neg (by change index.val ≠ 0; omega)]
          rw [if_neg (by change ¬index.val < 131073; omega)]
          rw [if_pos (by change index.val < 262145; omega)]
          rfl
        rw [view]
        exact actual
      ·
        by_cases selected3 : index.val < 393217
        ·
          have actual := region3_row ⟨index.val - 262145, by have := index.isLt; omega⟩
          have position : 262145 + (index.val - 262145) = index.val := by omega
          simp only [position] at actual
          have view : Verification.importedSubwordRow index = Verification.loadHalfData.columns.map (fun column => (column.get? (index.val - 262145)).getD 0) := by
            unfold Verification.importedSubwordRow
            rw [if_pos (by change index.val < 655361; omega)]
            unfold Verification.subwordNativeRow
            rw [if_neg (by change index.val ≠ 0; omega)]
            rw [if_neg (by change ¬index.val < 131073; omega)]
            rw [if_neg (by change ¬index.val < 262145; omega)]
            rw [if_pos (by change index.val < 393217; omega)]
            rfl
          rw [view]
          exact actual
        ·
          by_cases selected4 : index.val < 655361
          ·
            have actual := region4_row ⟨index.val - 393217, by have := index.isLt; omega⟩
            have position : 393217 + (index.val - 393217) = index.val := by omega
            simp only [position] at actual
            have view : Verification.importedSubwordRow index = Verification.loadByteData.columns.map (fun column => (column.get? (index.val - 393217)).getD 0) := by
              unfold Verification.importedSubwordRow
              rw [if_pos (by change index.val < 655361; omega)]
              unfold Verification.subwordNativeRow
              rw [if_neg (by change index.val ≠ 0; omega)]
              rw [if_neg (by change ¬index.val < 131073; omega)]
              rw [if_neg (by change ¬index.val < 262145; omega)]
              rw [if_neg (by change ¬index.val < 393217; omega)]
              rw [if_pos (by change index.val < 655361; omega)]
              rfl
            rw [view]
            exact actual
          ·
            by_cases selected5 : index.val < 4849665
            ·
              have actual := region5_row ⟨index.val - 655361, by have := index.isLt; omega⟩
              have position : 655361 + (index.val - 655361) = index.val := by omega
              simp only [position] at actual
              have view : Verification.importedSubwordRow index = Verification.subwordROMHalfData.columns.map (fun column => (column.get? (index.val - 655361)).getD 0) := by
                unfold Verification.importedSubwordRow
                rw [if_neg (by change ¬index.val < 655361; omega)]
                rw [if_pos (by change index.val < 4849665; omega)]
                rfl
              rw [view]
              exact actual
            ·
              have actual := region6_row ⟨index.val - 4849665, by have := index.isLt; omega⟩
              have position : 4849665 + (index.val - 4849665) = index.val := by omega
              simp only [position] at actual
              have view : Verification.importedSubwordRow index = Verification.subwordROMByteData.columns.map (fun column => (column.get? (index.val - 4849665)).getD 0) := by
                unfold Verification.importedSubwordRow
                rw [if_neg (by change ¬index.val < 655361; omega)]
                rw [if_neg (by change ¬index.val < 4849665; omega)]
                rfl
              rw [view]
              exact actual

end Airbender.Compiler.ROMNative.SubwordRows
