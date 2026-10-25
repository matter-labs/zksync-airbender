import GKRProtocol.ROMNative.UnifiedValues
import GKRProtocol.ROMNative.UnifiedTag
import Airbender.Proofs.UnifiedReduced.Tables.ImportedROM

namespace Airbender.Compiler.ROMNative.Unified
open Airbender Airbender.Compiler Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev nativeSetup := Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model

theorem rom_column (column : Fin 10) (index : Fin 1048576) :
    nativeSetup.imported.data.columns[column.val].get? (590081 + index.val) =
      UnifiedReduced.Setup.nativeROMData.columns[column.val].get? index.val := by
  fin_cases column
  · exact UnifiedValues.column0 index
  · exact UnifiedValues.column1 index
  · exact UnifiedValues.column2 index
  · exact UnifiedValues.column3 index
  · exact UnifiedValues.column4 index
  · exact UnifiedValues.column5 index
  · exact UnifiedValues.column6 index
  · exact UnifiedValues.column7 index
  · exact UnifiedValues.column8 index
  · exact UnifiedValues.column9 index

theorem rom_row (index : Fin 1048576) :
    (nativeSetup.imported.data.row ⟨590081 + index.val, by have := index.isLt; change 590081 + index.val < 8388608; omega⟩).map
      (fun n : Int => (n : Source.BaseField)) =
    (UnifiedReduced.Setup.nativeROMData.columns.map (fun column => (column.get? index.val).getD 0)).map
      (fun n : Nat => (n : Source.BaseField)) := by
  apply Vector.ext
  intro column bound
  simp only [TableData.row, Vector.getElem_map,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [Setup.signedValue_cast, rom_column ⟨column, bound⟩ index]

theorem active_rom_refinement {query : Vector Source.BaseField 10}
    (member : (nativeSetup.imported.data.table "Airbender.Native.UnifiedReduced").Contains #[] query)
    (tag : query[9] = 34) :
    (UnifiedReduced.Setup.importedTable (p := babyBearModulus)).Contains #[] query := by
  obtain ⟨row, equal⟩ := member
  change query = (nativeSetup.imported.data.row row).map (fun n : Int => (n : Source.BaseField)) at equal
  have selected : nativeSetup.value row (.generic 9) = 34 := by
    rw [← tag, equal, nativeSetup.value_generic row (⟨9, by decide⟩ : Fin 10)]
    simp only [Vector.getElem_map]
  have bounds := UnifiedTag.rom_region row selected
  let index : Fin 1048576 := ⟨row.val - 590081, by omega⟩
  have position : row = ⟨590081 + index.val, by change 590081 + index.val < 8388608; have := index.isLt; omega⟩ :=
    Fin.ext (by dsimp [index]; omega)
  rw [position, rom_row] at equal
  refine ⟨⟨1048961 + index.val, by change 1048961 + index.val < 2097537; have := index.isLt; omega⟩, equal.trans ?_⟩
  change _ = (UnifiedReduced.Setup.importedRow ⟨1048961 + index.val, _⟩).map (fun n : Nat => (n : Source.BaseField))
  simp only [UnifiedReduced.Setup.importedRow, dif_neg (by omega : ¬1048961 + index.val < 1048961),
    Nat.add_sub_cancel_left]

theorem public_rom_refinement {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {query : Vector Source.BaseField 10}
    (member : (nativeSetup.imported.data.table "Airbender.Native.UnifiedReduced").Contains #[] query)
    (tag : query[9] = 34) :
    (UnifiedReduced.Setup.table (p := babyBearModulus) before).Contains #[] query := by
  rw [← UnifiedReduced.Setup.Proofs.imported_table_before image]
  exact active_rom_refinement member tag

end Airbender.Compiler.ROMNative.Unified
