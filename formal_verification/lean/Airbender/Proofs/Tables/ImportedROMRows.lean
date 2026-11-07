import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Circuits.WordMemory.Tables.Setup
import Airbender.Proofs.Tables.ImportedROMProgram

namespace Airbender.Trace.ROM.Proofs
open Verification Arithmetic Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

theorem selectedWord_bound (index : Nat) (bound : index < 1048576) :
    selectedWord index < 4294967296 := by
  by_cases early : index < 4
  · interval_cases index <;> decide +kernel
  · rw [selectedWord_zero index (by omega) bound]
    decide

theorem imported_word_cast_row {p : Nat} (index : Nat) (bound : index < 1048576) :
    ((nativeWordData.row ⟨index, bound⟩).map (fun n : Int => (n : ZMod p))) =
      (#v[4 * index, selectedWord index % 65536, selectedWord index / 65536,
        0, 0, 0, 0, 0, 34] : Vector Nat 9).map (fun n : Nat => (n : ZMod p)) := by
  have actual := imported_word_rom_row index bound
  have converted := congrArg (Vector.map fun n => (signedValue n : ZMod p)) actual
  have wordBound := selectedWord_bound index bound
  have addressBound : 4 * index ≤ babyBearModulus / 2 := by
    change 4 * index ≤ 1006632960
    omega
  have lowBound : selectedWord index % 65536 ≤ babyBearModulus / 2 := by
    have := Nat.mod_lt (selectedWord index) (by decide : 0 < 65536)
    change _ ≤ 1006632960
    omega
  have highBound : selectedWord index / 65536 ≤ babyBearModulus / 2 := by
    change _ ≤ 1006632960
    omega
  simpa [TableData.row, show nativeWordData.offset = 0 by rfl,
    Vector.map_map, Function.comp_def, signedValue,
    addressBound, lowBound, highBound, show 34 ≤ babyBearModulus / 2 by decide] using converted

private theorem importedRow_zero (index : Fin (nativeWordZeroData.length + nativeWordData.length))
    (zero : index.val = 0) : importedRow index = Vector.replicate 9 (0 : Int) := by
  have position : index = ⟨0, by decide +kernel⟩ := Fin.ext zero
  rw [position]
  decide +kernel

/-- Complete logical membership characterization of the imported disabled/ROM
    regions. Every output is recovered from the imported public image. -/
theorem imported_member {p : Nat} [Fact p.Prime] {query : Vector (ZMod p) 9}
    (member : (importedTable (p := p)).Contains #[] query) :
    query = Vector.replicate 9 0 ∨ ∃ n : Fin 1048576,
      query = (#v[4 * n.val, selectedWord n.val % 65536, selectedWord n.val / 65536,
        0, 0, 0, 0, 0, 34] : Vector Nat 9).map (fun value : Nat => (value : ZMod p)) := by
  obtain ⟨index, equal⟩ := member
  change query = (importedRow index).map (fun n : Int => (n : ZMod p)) at equal
  by_cases zero : index.val < nativeWordZeroData.length
  · left
    have atZero : index.val = 0 := by change index.val < 1 at zero; omega
    rw [importedRow_zero index atZero] at equal
    simpa only [Vector.map_replicate, Int.cast_zero] using equal
  · right
    let n := index.val - nativeWordZeroData.length
    have bound : n < 1048576 := by have := index.isLt; change index.val < 1048577 at this; change index.val - 1 < 1048576; omega
    refine ⟨⟨n, bound⟩, ?_⟩
    exact equal.trans (by simpa only [importedRow, dif_neg zero] using imported_word_cast_row (p := p) n bound)

theorem imported_bounds {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    {query : Vector (ZMod p) 9} (member : (importedTable (p := p)).Contains #[] query) :
    query[1].val < 65536 ∧ query[2].val < 65536 := by
  rcases imported_member member with rfl | ⟨index, rfl⟩
  · simp
  · have word := selectedWord_bound index.val index.isLt
    have low : selectedWord index.val % 65536 < 65536 := Nat.mod_lt _ (by decide)
    have high : selectedWord index.val / 65536 < 65536 := by omega
    simpa only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ,
      ZMod.val_natCast_of_lt (show selectedWord index.val % 65536 < p by omega),
      ZMod.val_natCast_of_lt (show selectedWord index.val / 65536 < p by omega)] using And.intro low high

theorem imported_disabled {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    {query : Vector (ZMod p) 9} (member : (importedTable (p := p)).Contains #[] query)
    (inactive : query[8] = 0) : query[1] = 0 ∧ query[2] = 0 := by
  rcases imported_member member with rfl | ⟨index, rfl⟩
  · exact ⟨rfl, rfl⟩
  · have tag : (34 : ZMod p) = 0 := by simpa using inactive
    have divides := (ZMod.natCast_eq_zero_iff 34 p).mp tag
    have := Nat.le_of_dvd (by decide : 0 < 34) divides
    omega

end Airbender.Trace.ROM.Proofs
