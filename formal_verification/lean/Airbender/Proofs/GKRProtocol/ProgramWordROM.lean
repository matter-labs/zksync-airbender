import Airbender.Proofs.GKRProtocol.NativeProgramQueries
import Airbender.Proofs.GKRProtocol.ROMNative.WordFullRows
import Airbender.Proofs.GKRProtocol.PhysicalClosedNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.PhysicalClosedNative.WordMemoryCached

namespace Airbender.Compiler.NativeProgramSetup
open Airbender.Reference.Compiler Airbender.Trace
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem vector_nine_last (query : Vector Source.BaseField 9) :
    query.toList.getLast?.getD 0 = query[8] := by
  simp [List.getLast?_eq_getElem?]

/-- The captured word table has only the ROM tag and zero outside the decoder. -/
theorem fixed_word_query_zero (configuration : Configuration)
    (which : configuration = .wordMemoryUncached ∨ configuration = .wordMemoryCached)
    (index : Fin (lookupLength configuration)) (query : Vector Source.BaseField 9)
    (same : query.toList = retainedRows configuration 0 index.val)
    (notDecoder : query[8] ≠ 46) (notROM : query[8] ≠ 34) :
    query = Vector.replicate 9 0 := by
  have captured : ROMNative.WordFullPublic.nativeSetup.Contains
      ((List.range 9).map SourceSetupColumn.generic) query.toList := by
    rcases which with rfl | rfl
    · refine ⟨index, ?_⟩
      have bounded : index.val < MaterializedNative.WordMemoryUncached.native.model.imported.data.length := index.isLt
      simp only [retainedRows, dif_pos bounded] at same
      change query.toList = MaterializedNative.WordMemoryUncached.native.model.fields
        TableNative.WordMemoryUncached.native.genericSetupColumns index at same
      rw [PhysicalClosedNative.WordMemoryUncached.generic_columns_inventory] at same
      exact same
    · refine ⟨index, ?_⟩
      have bounded : index.val < MaterializedNative.WordMemoryCached.native.model.imported.data.length := index.isLt
      simp only [retainedRows, dif_pos bounded] at same
      change query.toList = MaterializedNative.WordMemoryCached.native.model.fields
        TableNative.WordMemoryCached.native.genericSetupColumns index at same
      rw [PhysicalClosedNative.WordMemoryCached.generic_columns_inventory] at same
      exact same
  have checked := ROMNative.WordFullPublic.nativeSetup.generic_clean_contains
    ((List.range 9).map SourceSetupColumn.generic) rfl query captured "Airbender.Native.WordMemory" #[]
  rcases ROM.Proofs.imported_member (ROMNative.WordFullPublic.full_refinement checked notDecoder) with
    zero | ⟨wordIndex, equal⟩
  · exact zero
  · apply False.elim
    apply notROM
    rw [equal]
    simp

/-- Every native non-decoder word query is zero or reads the public word function. -/
theorem word_query_member (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (configuration : Configuration)
    (which : configuration = .wordMemoryUncached ∨ configuration = .wordMemoryCached)
    (index : Fin (lookupLength configuration)) (query : Vector Source.BaseField 9)
    (same : query.toList = rows decoder wordAt configuration 0 index.val)
    (notDecoder : query[8] ≠ 46) :
    query = Vector.replicate 9 0 ∨ ∃ wordIndex : Fin 1048576,
      query.toList = ProgramSetup.packTagged 9 34 (ProgramSetup.romPayload wordAt wordIndex.val) := by
  let layout : ProgramSetup.Layout := {
    «width» := 9, tagged := true, decoderStart := 1048577,
    decoderWords := 1048576, romStart := some 1, romWords := 1048576 }
  have selected : layouts configuration = some layout := by
    rcases which with rfl | rfl <;> rfl
  by_cases rom : query[8] = 34
  · have genericSame : query.toList = ProgramSetup.genericRows layout
        (retainedRows configuration 0) (decoder configuration) wordAt index.val := by
      simpa [rows, selected, ProgramSetup.groupRows] using same
    obtain ⟨regionStart, region, inside, equal⟩ := ProgramSetup.rom_query_region layout
      (retainedRows configuration 0) (decoder configuration) wordAt index.val rfl
      (by exact of_decide_eq_true rfl) (by exact of_decide_eq_true rfl) query.toList genericSame
      ((vector_nine_last query).trans rom)
    have atOne : regionStart = 1 := by simpa [layout] using region.symm
    subst regionStart
    exact Or.inr ⟨⟨index.val - 1, inside.2⟩, equal⟩
  · have notDecoderTag : query.toList.getLast?.getD 0 ≠ 46 := by
      simpa only [vector_nine_last] using notDecoder
    have notROMTag : query.toList.getLast?.getD 0 ≠ 34 := by
      simpa only [vector_nine_last] using rom
    rcases fixed_or_zero_member decoder wordAt configuration layout selected rfl index.val
      query.toList same notDecoderTag notROMTag with fixed | zero
    · exact Or.inl (fixed_word_query_zero configuration which index query fixed notDecoder rom)
    · left
      apply Vector.toList_inj.mp
      simpa [layout] using zero

/-- Public initial-image construction supplies every matched native ROM word. -/
theorem word_public_member {initial : Reference.RiscV.Sail.State} {cells : List Cell}
    {tokens : List (MemoryToken babyBearModulus)}
    (image : initialImage initial cells = some tokens)
    (domain : ROMNative.WordFullPublic.CoversROM cells)
    (decoder : Configuration → List (List Source.BaseField)) (configuration : Configuration)
    (which : configuration = .wordMemoryUncached ∨ configuration = .wordMemoryCached)
    (index : Fin (lookupLength configuration)) (query : Vector Source.BaseField 9)
    (same : query.toList = rows decoder (ROM.words initial) configuration 0 index.val)
    (notDecoder : query[8] ≠ 46) : (ROM.table cells tokens).Contains #[] query := by
  suffices present : query ∈ ROM.rows cells tokens by
    obtain ⟨row, equal⟩ := List.mem_iff_get.mp present
    exact ⟨row, equal.symm⟩
  rcases word_query_member decoder (ROM.words initial) configuration which index query same notDecoder with
    rfl | ⟨wordIndex, equal⟩
  · exact List.mem_cons_self
  · let address := BitVec.ofNat 32 (4 * wordIndex.val)
    have small : 4 * wordIndex.val < 2 ^ 32 := by have := wordIndex.isLt; omega
    have addressNat : address.toNat = 4 * wordIndex.val := Nat.mod_eq_of_lt small
    obtain ⟨_, _, bits, read, _⟩ := Trace.Proofs.image_cell_source image (Cell.ram address) (domain wordIndex)
    have publicWord : ROM.words initial wordIndex.val = bits := by
      have found := ROM.Proofs.words_at_address (by rw [addressNat]; omega) read
      simpa only [addressNat, Nat.mul_div_cancel_left _ (by decide : 0 < 4)] using found
    have shape : query = ROM.row address (Arithmetic.Word.ofBitVec bits) := by
      apply Vector.toList_inj.mp
      rw [equal]
      simp [ProgramSetup.packTagged, ProgramSetup.romPayload, publicWord,
        ROM.row, Arithmetic.Word.ofBitVec, Arithmetic.limbBase, addressNat]
    rw [shape]
    apply List.mem_cons_of_mem
    apply List.mem_filterMap.mpr
    refine ⟨(Cell.ram address, (Cell.ram address).initialToken bits),
      ROMNative.WordFullPublic.image_zip_member image (domain wordIndex) read, ?_⟩
    simp only [addressNat, Trace.Proofs.initial_token_word]
    rw [if_pos (by have := wordIndex.isLt; dsimp [ROM.limit]; omega)]

end Airbender.Compiler.NativeProgramSetup
