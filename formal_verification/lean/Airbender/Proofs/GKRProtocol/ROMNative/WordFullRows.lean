import Airbender.Review.Compiler.ROMDomain
import Airbender.Proofs.GKRProtocol.ROMNative.WordMemoryRows
import Airbender.Proofs.Trace.ROM

namespace Airbender.Compiler.ROMNative.WordFullPublic
open Airbender Airbender.Compiler Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

abbrev nativeSetup := WordMemory.nativeSetup

private theorem padding_last_bound (column : Fin 9) :
    0 < nativeSetup.imported.data.columns[column.val].blocks.size := by
  fin_cases column <;> decide +kernel

private theorem padding_prefix (column : Fin 9) :
    ((nativeSetup.imported.data.columns[column.val].blocks.toList.take
      (nativeSetup.imported.data.columns[column.val].blocks.size - 1)).map Block.length).sum =
      2097153 := by
  fin_cases column <;> decide +kernel

private theorem padding_last (column : Fin 9) :
    nativeSetup.imported.data.columns[column.val].blocks[
      nativeSetup.imported.data.columns[column.val].blocks.size - 1]'(by
        have := padding_last_bound column; omega) = .affine 14680063 0 0 := by
  fin_cases column <;> rfl

theorem padding_zero (row : Fin 16777216) (lower : 2097153 ≤ row.val) :
    (nativeSetup.imported.data.row row).map (fun n : Int => (n : Source.BaseField)) =
      Vector.replicate 9 0 := by
  apply Vector.ext
  intro column bound
  let lane : Fin 9 := ⟨column, bound⟩
  let data := nativeSetup.imported.data.columns[column]
  have lastBound : data.blocks.size - 1 < data.blocks.size := by
    have := padding_last_bound lane
    change 0 < data.blocks.size at this
    omega
  have shape : data.blocks[data.blocks.size - 1]'lastBound = .affine 14680063 0 0 :=
    padding_last lane
  have actual := column_block_value data ⟨data.blocks.size - 1, lastBound⟩
    2097153 row.val (padding_prefix lane) lower (by
      rw [shape]
      have := row.isLt
      change row.val - 2097153 < 14680063
      omega)
  rw [shape] at actual
  have zero := actual.trans (constant_block_get _ _ _ (by have := row.isLt; omega))
  simp only [TableData.row, Vector.getElem_map, Vector.getElem_replicate,
    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]
  change ((signedValue ((data.get? row.val).getD 0) : Int) : Source.BaseField) = 0
  rw [zero]
  rfl

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

end Airbender.Compiler.ROMNative.WordFullPublic
