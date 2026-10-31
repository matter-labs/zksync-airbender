import Airbender.Proofs.GKRProtocol.NativeProgramQueries
import Airbender.Proofs.GKRProtocol.ROMNative.UnifiedBoundary
import Airbender.Proofs.UnifiedReduced.Tables.ImportedROMRows
import Airbender.Proofs.GKRProtocol.PhysicalClosedNative.UnifiedUncached
import Airbender.Proofs.GKRProtocol.PhysicalClosedNative.UnifiedCached

namespace Airbender.Compiler.NativeProgramSetup
open Airbender.Reference.Compiler Airbender.Trace
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

private theorem rom_row_tag (address low high : Nat) :
    (((#v[address, low, high, 0, 0, 0, 0, 0, 0, 34] : Vector Nat 10).map
      (fun value : Nat => (value : Source.BaseField)))[9]) = 34 := by
  simp

private theorem rom_payload_row (wordAt : Nat → BitVec 32) (wordIndex : Nat) :
    ProgramSetup.packTagged 10 (34 : Source.BaseField) (ProgramSetup.romPayload wordAt wordIndex) =
      (((#v[4 * wordIndex, (wordAt wordIndex).toNat % 65536, (wordAt wordIndex).toNat / 65536,
        0, 0, 0, 0, 0, 0, 34] : Vector Nat 10).map
          (fun value : Nat => (value : Source.BaseField))).toList) := by
  simp [ProgramSetup.packTagged, ProgramSetup.romPayload]

theorem vector_ten_last (query : Vector Source.BaseField 10) :
    query.toList.getLast?.getD 0 = query[9] := by
  simp [List.getLast?_eq_getElem?]

/-- A captured fixed helper row belongs to the same table for every public image. -/
theorem unified_fixed_query_member (initial : Reference.RiscV.Sail.State)
    (configuration : Configuration)
    (which : configuration = .unifiedUncached ∨ configuration = .unifiedCached)
    (index : Fin (lookupLength configuration)) (query : Vector Source.BaseField 10)
    (same : query.toList = retainedRows configuration 0 index.val)
    (notDecoder : query[9] ≠ 46) (notROM : query[9] ≠ 34) :
    (UnifiedReduced.Setup.table initial).Contains #[] query := by
  have captured : ROMNative.UnifiedBoundary.nativeSetup.Contains
      ((List.range 10).map SourceSetupColumn.generic) query.toList := by
    rcases which with rfl | rfl
    · refine ⟨index, ?_⟩
      have bounded : index.val < MaterializedNative.UnifiedUncached.native.model.imported.data.length := index.isLt
      simp only [retainedRows, dif_pos bounded] at same
      change query.toList = MaterializedNative.UnifiedUncached.native.model.fields
        TableNative.UnifiedUncached.native.genericSetupColumns index at same
      rw [PhysicalClosedNative.UnifiedUncached.generic_columns_inventory] at same
      exact same
    · refine ⟨index, ?_⟩
      have bounded : index.val < MaterializedNative.UnifiedCached.native.model.imported.data.length := index.isLt
      simp only [retainedRows, dif_pos bounded] at same
      change query.toList = MaterializedNative.UnifiedCached.native.model.fields
        TableNative.UnifiedCached.native.genericSetupColumns index at same
      rw [PhysicalClosedNative.UnifiedCached.generic_columns_inventory] at same
      exact same
  have checked := ROMNative.UnifiedBoundary.nativeSetup.generic_clean_contains
    ((List.range 10).map SourceSetupColumn.generic) rfl query captured "Airbender.Native.UnifiedReduced" #[]
  obtain ⟨row, equal⟩ := ROMNative.UnifiedBoundary.full_table_refinement checked notDecoder
  change query = (UnifiedReduced.Setup.importedRow row).map (fun value : Nat => (value : Source.BaseField)) at equal
  by_cases fixed : row.val < 1048961
  · refine ⟨row, ?_⟩
    change query = (UnifiedReduced.Setup.row initial row).map (fun value : Nat => (value : Source.BaseField))
    simpa only [UnifiedReduced.Setup.importedRow, UnifiedReduced.Setup.row, dif_pos fixed] using equal
  · have shape : UnifiedReduced.Setup.importedRow row =
        (#v[4 * (row.val - 1048961), ROM.Proofs.selectedWord (row.val - 1048961) % 65536,
          ROM.Proofs.selectedWord (row.val - 1048961) / 65536, 0, 0, 0, 0, 0, 0, 34] : Vector Nat 10) := by
      calc
        UnifiedReduced.Setup.importedRow row = UnifiedReduced.Setup.nativeROMData.columns.map
            (fun column => (column.get? (row.val - 1048961)).getD 0) := by
          simp only [UnifiedReduced.Setup.importedRow, dif_neg fixed]
        _ = _ := UnifiedReduced.Setup.Proofs.imported_rom_row (row.val - 1048961) (by
          have bounded : row.val < 2097537 := row.isLt
          omega)
    apply False.elim
    apply notROM
    calc
      query[9] = ((UnifiedReduced.Setup.importedRow row).map (fun value : Nat => (value : Source.BaseField)))[9] :=
        congrArg (fun values : Vector Source.BaseField 10 => values[9]) equal
      _ = 34 := by rw [shape]; exact rom_row_tag _ _ _

/-- Zero padding belongs to the public unified table. -/
theorem unified_zero_member (initial : Reference.RiscV.Sail.State) :
    (UnifiedReduced.Setup.table initial).Contains #[] (Vector.replicate 10 (0 : Source.BaseField)) := by
  refine ⟨0, ?_⟩
  have zero : UnifiedReduced.Setup.row initial 0 = Vector.replicate 10 0 := by
    change UnifiedReduced.Setup.fixedRow 0 = Vector.replicate 10 0
    decide +kernel
  change Vector.replicate 10 (0 : Source.BaseField) =
    (UnifiedReduced.Setup.row initial 0).map (fun value : Nat => (value : Source.BaseField))
  rw [zero]
  simp

/-- Native non-decoder queries use the fixed helpers or public ROM words. -/
theorem unified_public_member (decoder : Configuration → List (List Source.BaseField))
    (initial : Reference.RiscV.Sail.State) (configuration : Configuration)
    (which : configuration = .unifiedUncached ∨ configuration = .unifiedCached)
    (index : Fin (lookupLength configuration)) (query : Vector Source.BaseField 10)
    (same : query.toList = rows decoder (ROM.words initial) configuration 0 index.val)
    (notDecoder : query[9] ≠ 46) : (UnifiedReduced.Setup.table initial).Contains #[] query := by
  let layout : ProgramSetup.Layout := {
    «width» := 10, tagged := true, decoderStart := 2097537,
    decoderWords := 1048576, romStart := some 590081, romWords := 1048576 }
  have selected : layouts configuration = some layout := by
    rcases which with rfl | rfl <;> rfl
  by_cases rom : query[9] = 34
  · have genericSame : query.toList = ProgramSetup.genericRows layout
        (retainedRows configuration 0) (decoder configuration) (ROM.words initial) index.val := by
      simpa [rows, selected, ProgramSetup.groupRows] using same
    obtain ⟨regionStart, region, inside, equal⟩ := ProgramSetup.rom_query_region layout
      (retainedRows configuration 0) (decoder configuration) (ROM.words initial) index.val rfl
      (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) query.toList genericSame
      ((vector_ten_last query).trans rom)
    have atROM : regionStart = 590081 := by simpa [layout] using region.symm
    subst regionStart
    have wordBound : index.val - 590081 < 1048576 := inside.2
    let publicIndex : Fin 2097537 := ⟨1048961 + (index.val - 590081), by omega⟩
    have outside : ¬ publicIndex.val < 1048961 := by dsimp [publicIndex]; omega
    have wordIndexEq : publicIndex.val - 1048961 = index.val - 590081 := by dsimp [publicIndex]; omega
    have publicRow : UnifiedReduced.Setup.row initial publicIndex =
        (#v[4 * (index.val - 590081), (ROM.words initial (index.val - 590081)).toNat % 65536,
          (ROM.words initial (index.val - 590081)).toNat / 65536, 0, 0, 0, 0, 0, 0, 34] : Vector Nat 10) := by
      simp only [UnifiedReduced.Setup.row, dif_neg outside, wordIndexEq,
        Arithmetic.Word.ofBitVec, Arithmetic.limbBase]
    refine ⟨publicIndex, ?_⟩
    change query = (UnifiedReduced.Setup.row initial publicIndex).map (fun value : Nat => (value : Source.BaseField))
    rw [publicRow]
    apply Vector.toList_inj.mp
    rw [equal]
    exact rom_payload_row (ROM.words initial) (index.val - 590081)
  · have notDecoderTag : query.toList.getLast?.getD 0 ≠ 46 := by
      simpa only [vector_ten_last] using notDecoder
    have notROMTag : query.toList.getLast?.getD 0 ≠ 34 := by
      simpa only [vector_ten_last] using rom
    rcases fixed_or_zero_member decoder (ROM.words initial) configuration layout selected rfl index.val
      query.toList same notDecoderTag notROMTag with fixed | zero
    · exact unified_fixed_query_member initial configuration which index query fixed notDecoder rom
    · have queryZero : query = Vector.replicate 10 0 := by
        apply Vector.toList_inj.mp
        simpa [layout] using zero
      rw [queryZero]
      exact unified_zero_member initial

end Airbender.Compiler.NativeProgramSetup
