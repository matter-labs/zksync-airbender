import GKRProtocol.ROMNative.WordMemoryPublic
import GKRProtocol.DecoderTail.WordMemory.Rows
import Airbender.Proofs.Trace.ROM

namespace Airbender.Compiler.ROMNative.WordFullPublic
open Airbender Airbender.Compiler Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

abbrev nativeSetup := WordMemory.nativeSetup

theorem padding_zero (row : Fin 16777216) (lower : 2097153 ≤ row.val) :
    (nativeSetup.imported.data.row row).map (fun n : Int => (n : Source.BaseField)) =
      Vector.replicate 9 0 := by
  apply Vector.ext
  intro column bound
  have position : 1048577 + (row.val - 1048577) = row.val := by omega
  have outside : ¬ row.val - 1048577 < Trace.NativeDecoder.wordMemorySetup.realRows.length := by
    change ¬ row.val - 1048577 < 1048576
    omega
  have actual := DecoderTail.WordMemory.Rows.tail_column ⟨column, bound⟩ (row.val - 1048577)
  rw [position, if_neg outside] at actual
  simp only [TableData.row, Vector.getElem_map, Vector.getElem_replicate,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  rw [actual, Setup.signedValue_cast]
  have paddingBound : row.val - 1048577 - 1048576 < 14680063 := by have := row.isLt; omega
  interval_cases column
  all_goals change ((getFromBlocks [.affine 14680063 0 0] (row.val - 1048577 - 1048576)).getD 0 : Source.BaseField) = 0
  all_goals simp only [getFromBlocks, Block.length, if_pos paddingBound,
    constant_block_get 14680063 0 _ paddingBound, Option.getD_some, Nat.cast_zero]


theorem full_refinement {query : Vector Source.BaseField 9}
    (member : (nativeSetup.imported.data.table "Airbender.Native.WordMemory").Contains #[] query)
    (notDecoder : query[8] ≠ 46) :
    (Trace.ROM.importedTable (p := babyBearModulus)).Contains #[] query := by
  obtain ⟨row, equal⟩ := member
  change query = (nativeSetup.imported.data.row row).map (fun n : Int => (n : Source.BaseField)) at equal
  by_cases first : row.val < 1
  · have position : row = ⟨0, by decide⟩ := Fin.ext (by change row.val = 0; omega)
    subst query
    rw [position]
    refine ⟨⟨0, by decide +kernel⟩, ?_⟩
    exact congrArg (fun values : Vector Int 9 => values.map (fun n : Int => (n : Source.BaseField)))
      (by decide +kernel : nativeSetup.imported.data.row (0 : Fin 16777216) = Trace.ROM.importedRow (0 : Fin 1048577))
  · by_cases rom : row.val < 1048577
    · let index : Fin 1048576 := ⟨row.val - 1, by omega⟩
      have position : row = ⟨1 + index.val, by have := index.isLt; change 1 + index.val < 16777216; omega⟩ :=
        Fin.ext (by dsimp [index]; omega)
      refine ⟨⟨1 + index.val, by have := index.isLt; change 1 + index.val < 1048577; omega⟩, ?_⟩
      rw [position, WordMemory.rom_row] at equal
      exact equal.trans (by
        simp only [Trace.ROM.importedRow]
        rw [dif_neg (by change ¬1 + index.val < 1; omega)]
        simp only [show Trace.ROM.nativeWordZeroData.length = 1 from rfl, Nat.add_sub_cancel_left]
        rfl)
    · by_cases decoder : row.val < 2097153
      · have selected : ((nativeSetup.imported.data.row row).map (fun n : Int => (n : Source.BaseField)))[8] = 46 := by
          simp only [TableData.row, Vector.getElem_map,
            show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
          rw [Setup.signedValue_cast]
          change (((getFromBlocks [.dense #[0], .affine 1048576 34 0,
            .affine 1048576 46 0, .affine 14680063 0 0] row.val).getD 0) : Source.BaseField) = 46
          have a : ¬ row.val < 1 := first
          have b : ¬ row.val - 1 < 1048576 := by omega
          have c : row.val - 1 - 1048576 < 1048576 := by omega
          simp only [getFromBlocks, Block.length, show (#[0] : Array Nat).size = 1 from rfl,
            if_neg a, if_neg b, if_pos c]
          rw [constant_block_get _ _ _ c]
          rfl
        exact False.elim (notDecoder (congrArg (fun values => values[8]) equal |>.trans selected))
      · have zero := padding_zero row (by omega)
        refine ⟨⟨0, by decide +kernel⟩, ?_⟩
        have firstZero : Trace.ROM.importedRow ⟨0, by decide +kernel⟩ = Vector.replicate 9 (0 : Int) := by decide +kernel
        change query = (Trace.ROM.importedRow ⟨0, by decide +kernel⟩).map (fun n : Int => (n : Source.BaseField))
        rw [firstZero, Vector.map_replicate, Int.cast_zero]
        exact equal.trans zero


/-- The public cell domain covers the complete ROM used by this retained
compiler capture. This is a domain premise, independent of witness values. -/
def CoversROM (cells : List Trace.Cell) : Prop :=
  ∀ index : Fin 1048576, Trace.Cell.ram (BitVec.ofNat 32 (4 * index.val)) ∈ cells

theorem image_zip_member {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {tokens : List (Trace.MemoryToken p)} (image : Trace.initialImage before cells = some tokens)
    {cell : Trace.Cell} (member : cell ∈ cells) {bits : BitVec 32}
    (read : cell.read before = .ok bits before) :
    (cell, cell.initialToken (p := p) bits) ∈ cells.zip tokens := by
  have reads := Trace.Proofs.image_reads image
  clear image
  induction reads with
  | nil => cases member
  | @cons head token cells tokens headEvidence tail ih =>
    rcases List.mem_cons.mp member with same | included
    · subst cell
      obtain ⟨value, found, rfl⟩ := headEvidence
      have equal : value = bits := (EStateM.Result.ok.inj (found.symm.trans read)).1
      subst value
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih included)

theorem imported_public_refinement {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {cells : List Trace.Cell}
    {tokens : List (Trace.MemoryToken babyBearModulus)}
    (physical : Trace.initialImage before cells = some tokens) (domain : CoversROM cells)
    {query : Vector Source.BaseField 9}
    (member : (Trace.ROM.importedTable (p := babyBearModulus)).Contains #[] query) :
    (Trace.ROM.table cells tokens).Contains #[] query := by
  suffices present : query ∈ Trace.ROM.rows cells tokens by
    obtain ⟨index, same⟩ := List.mem_iff_get.mp present
    exact ⟨index, same.symm⟩
  rcases Trace.ROM.Proofs.imported_member member with rfl | ⟨index, rfl⟩
  · exact List.mem_cons_self
  · let address := BitVec.ofNat 32 (4 * index.val)
    let bits := BitVec.ofNat 32 (Trace.ROM.Proofs.selectedWord index.val)
    have small : 4 * index.val < 2 ^ 32 := by have := index.isLt; omega
    have addressNat : address.toNat = 4 * index.val := Nat.mod_eq_of_lt small
    have read : (Trace.Cell.ram address).read before = .ok bits before := by
      change (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4 address.toNat).run before = _
      rw [addressNat]
      exact image ⟨index.val, index.isLt⟩
    have zipped := image_zip_member physical (domain index) read
    have wordBound := Trace.ROM.Proofs.selectedWord_bound index.val index.isLt
    have same : Trace.ROM.row (p := babyBearModulus) address (Arithmetic.Word.ofBitVec bits) =
        (#v[4 * index.val, Trace.ROM.Proofs.selectedWord index.val % 65536,
          Trace.ROM.Proofs.selectedWord index.val / 65536, 0, 0, 0, 0, 0, 34] : Vector Nat 9).map
            (fun n : Nat => (n : Source.BaseField)) := by
      simp [Trace.ROM.row, Arithmetic.Word.ofBitVec, bits, addressNat,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordBound, Arithmetic.limbBase]
    rw [← same]
    apply List.mem_cons_of_mem
    apply List.mem_filterMap.mpr
    refine ⟨(Trace.Cell.ram address, (Trace.Cell.ram address).initialToken bits), zipped, ?_⟩
    simp only [addressNat, Trace.Proofs.initial_token_word]
    rw [if_pos (by have := index.isLt; dsimp [Trace.ROM.limit]; omega)]

theorem public_refinement {before : Reference.RiscV.Sail.State}
    (image : Trace.ROM.ImportedImage before) {cells : List Trace.Cell}
    {tokens : List (Trace.MemoryToken babyBearModulus)}
    (physical : Trace.initialImage before cells = some tokens) (domain : CoversROM cells)
    {query : Vector Source.BaseField 9}
    (member : (nativeSetup.imported.data.table "Airbender.Native.WordMemory").Contains #[] query)
    (notDecoder : query[8] ≠ 46) :
    (Trace.ROM.table cells tokens).Contains #[] query :=
  imported_public_refinement image physical domain (full_refinement member notDecoder)

end Airbender.Compiler.ROMNative.WordFullPublic
