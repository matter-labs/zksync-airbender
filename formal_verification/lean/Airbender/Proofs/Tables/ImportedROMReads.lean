import Airbender.Review.Helpers.Memory.ImportedImage
import Airbender.Review.Circuits.WordMemory.Tables.Setup
import Airbender.Proofs.Tables.ImportedROMProgram

namespace Airbender.Trace.ROM.Proofs
open Verification Arithmetic Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

theorem imported_image_words {before : Reference.RiscV.Sail.State}
    (image : ImportedImage before) (index : Nat) (bound : index < 1048576) :
    words before index = importedWords index := by
  unfold words
  rw [image ⟨index, bound⟩]
  rfl

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

theorem imported_bounds {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
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

theorem imported_disabled {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {query : Vector (ZMod p) 9} (member : (importedTable (p := p)).Contains #[] query)
    (inactive : query[8] = 0) : query[1] = 0 ∧ query[2] = 0 := by
  rcases imported_member member with rfl | ⟨index, rfl⟩
  · exact ⟨rfl, rfl⟩
  · have tag : (34 : ZMod p) = 0 := by simpa using inactive
    have divides := (ZMod.natCast_eq_zero_iff 34 p).mp tag
    have := Nat.le_of_dvd (by decide : 0 < 34) divides
    omega

/-- A native accepted word-ROM query reads the public image. All lookup outputs
    and addresses are recovered from actual imported rows. -/
theorem imported_reads {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {before : Reference.RiscV.Sail.State} (image : ImportedImage before) :
    Reads before (importedTable (p := p)) := by
  intro address lo hi bounded high member
  change ∃ index : Fin (nativeWordZeroData.length + nativeWordData.length),
    #v[(address.lo : ZMod p) + 65536 * address.hi, lo, hi, 0, 0, 0, 0, 0, 34] =
      (importedRow index).map (fun n : Int => (n : ZMod p)) at member
  obtain ⟨index, equal⟩ := member
  by_cases zero : index.val < nativeWordZeroData.length
  · have tag := congrArg (fun row : Vector (ZMod p) 9 => row[8]) equal
    have atZero : index.val = 0 := by change index.val < 1 at zero; omega
    have bad : (34 : ZMod p) = 0 := by
      rw [importedRow_zero index atZero] at tag
      simpa using tag
    have divides : p ∣ 34 := (ZMod.natCast_eq_zero_iff 34 p).mp bad
    have := Nat.le_of_dvd (by decide : 0 < 34) divides
    omega
  · let n := index.val - nativeWordZeroData.length
    have nBound : n < 1048576 := by have := index.isLt; change index.val < 1048577 at this; change index.val - 1 < 1048576; omega
    have actual : (importedRow index).map (fun n : Int => (n : ZMod p)) =
        (#v[4 * n, selectedWord n % 65536, selectedWord n / 65536,
          0, 0, 0, 0, 0, 34] : Vector Nat 9).map (fun n : Nat => (n : ZMod p)) := by
      simpa only [importedRow, dif_neg zero] using imported_word_cast_row (p := p) n nBound
    rw [actual] at equal
    have addressEq := congrArg (fun row : Vector (ZMod p) 9 => row[0]) equal
    have loEq := congrArg (fun row : Vector (ZMod p) 9 => row[1]) equal
    have hiEq := congrArg (fun row : Vector (ZMod p) 9 => row[2]) equal
    have valueBound := selectedWord_bound n nBound
    have addressBound : address.value < p := by
      have boundLo : address.lo < 65536 := bounded.1
      change address.lo + 65536 * address.hi < p
      omega
    have canonicalAddress : address.value = 4 * n := by
      have same : (address.value : ZMod p) = (4 * n : Nat) := by
        simpa [Word.value, limbBase, Nat.cast_add, Nat.cast_mul] using addressEq
      have values := congrArg ZMod.val same
      simpa only [ZMod.val_natCast_of_lt addressBound,
        ZMod.val_natCast_of_lt (show 4 * n < p by omega)] using values
    have canonicalLow : lo.val = selectedWord n % 65536 := by
      have values := congrArg ZMod.val loEq
      simpa [ZMod.val_natCast,
        Nat.mod_eq_of_lt (show selectedWord n % 65536 < p by
          have := Nat.mod_lt (selectedWord n) (by decide : 0 < 65536)
          omega)] using values
    have canonicalHigh : hi.val = selectedWord n / 65536 := by
      have values := congrArg ZMod.val hiEq
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (show selectedWord n / 65536 < p by omega)] using values
    have addressNat : address.toBitVec.toNat = 4 * n := by
      simp [Word.toBitVec, canonicalAddress, BitVec.toNat_ofNat]
      omega
    rw [addressNat]
    have expected : (Word.mk lo.val hi.val).toBitVec = BitVec.ofNat 32 (selectedWord n) := by
      simp only [Word.toBitVec, Word.value, limbBase, canonicalLow, canonicalHigh]
      congr 1
      omega
    rw [expected]
    exact image ⟨n, nBound⟩

end Airbender.Trace.ROM.Proofs
