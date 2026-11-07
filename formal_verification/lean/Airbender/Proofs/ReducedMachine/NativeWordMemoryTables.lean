import Airbender.Proofs.ReducedMachine.NativePool
import Airbender.Review.Circuits.ReducedMachine.Tables.WordMemory
import Airbender.Proofs.Tables.PeriodicColumns
import Mathlib.Tactic.IntervalCases

namespace Airbender.ReducedMachine.NativeWordMemoryTableProofs
open NativeFixed Setup Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

private theorem single_get (block : Block) (n : Nat) (bound : n < block.length) :
    (⟨#[block]⟩ : Column).get? n = block.get? n := by
  change getFromBlocks [block] n = _
  rw [getFromBlocks, if_pos bound]

/-- Every one of the 65,536 actual offset rows, proved by the stored periods. -/
theorem offset_rows (i : Fin 65536) : dataT18.rowNat i = wordOffsetRow i.val := by
  have key : dataT18.columns[0].get? i.val = some i.val := by
    change (⟨#[.affine 65536 0 1]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 65536 0 1 i.val i.isLt
  have low : dataT18.columns[1].get? i.val = some (i.val % 2) := by
    change (⟨#[.periodic 32768 0 #[0,1]]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    have read := Setup.Proofs.periodic_get #[0,1] 32768 0 i.val (by decide) i.isLt
    change Block.get? (.periodic 32768 0 #[0,1]) i.val = _ at read
    rw [read]
    have cases : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
    rcases cases with h | h <;> simp [h]
  have high : dataT18.columns[2].get? i.val = some (i.val / 2 % 2) := by
    change (⟨#[.periodic 16384 0 #[0,0,1,1]]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    have read := Setup.Proofs.periodic_get #[0,0,1,1] 16384 0 i.val (by decide) i.isLt
    change Block.get? (.periodic 16384 0 #[0,0,1,1]) i.val = _ at read
    rw [read]
    have cases : i.val % 4 = 0 ∨ i.val % 4 = 1 ∨ i.val % 4 = 2 ∨ i.val % 4 = 3 := by omega
    rcases cases with h | h | h | h <;> simp [h] <;> omega
  have tag : dataT18.columns[3].get? i.val = some 18 := by
    change (⟨#[.affine 65536 18 0]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 65536 18 0 i.val i.isLt
  apply Vector.ext
  intro lane bound
  interval_cases lane <;> simp [TableData.rowNat,wordOffsetRow,key,low,high,tag]

/-- Every separator row. High limbs below 64 are ROM; all others are RAM.
    Both classes retain the high limb modulo 64 as the ROM shadow address. -/
theorem separator_rows (i : Fin 65536) : dataT23.rowNat i = wordSeparatorRow i.val := by
  have key : dataT23.columns[0].get? i.val = some i.val := by
    change (⟨#[.affine 65536 0 1]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 65536 0 1 i.val i.isLt
  have ram : dataT23.columns[1].get? i.val = some (if i.val < 64 then 0 else 1) := by
    change getFromBlocks [.affine 64 0 0,.affine 65472 1 0] i.val = _
    by_cases first : i.val < 64
    · rw [getFromBlocks]
      simp only [Block.length]
      rw [if_pos first]
      simpa [first] using affine_get 64 0 0 i.val first
    · rw [getFromBlocks]
      simp only [Block.length]
      rw [if_neg first,getFromBlocks]
      simp only [Block.length]
      rw [if_pos (by have := i.isLt; omega)]
      simpa [first] using affine_get 65472 1 0 (i.val-64) (by have := i.isLt; omega)
  have shadow : dataT23.columns[2].get? i.val = some (i.val % 64) := by
    change (⟨#[.periodic 1024 0 (Array.range 64)]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    have read := Setup.Proofs.periodic_get (Array.range 64) 1024 0 i.val (by decide) i.isLt
    change Block.get? (.periodic 1024 0 (Array.range 64)) i.val = _ at read
    rw [read]
    simp
  have tag : dataT23.columns[3].get? i.val = some 23 := by
    change (⟨#[.affine 65536 23 0]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 65536 23 0 i.val i.isLt
  apply Vector.ext
  intro lane bound
  interval_cases lane <;> simp [TableData.rowNat,wordSeparatorRow,key,ram,shadow,tag]

/-- Every actual native ROM row, including the full repeated padding tail. -/
theorem rom_rows (i : Fin 1048576) : dataT24.rowNat i = wordROMRow i.val := by
  have key : dataT24.columns[0].get? i.val = some (4*i.val) := by
    change (⟨#[.affine 1048576 0 4]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 1048576 0 4 i.val i.isLt
  have value : dataT24.columns[1].get? i.val = some (wordROMValue i.val)[0] ∧
      dataT24.columns[2].get? i.val = some (wordROMValue i.val)[1] := by
    by_cases first : i.val < 7
    · have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 := by omega
      rcases cases with h | h | h | h | h | h | h <;> simp [h,wordROMValue,Column.get?,getFromBlocks,Block.length,Block.get?,dataT24,dataT24Column1,dataT24Column2,dataT24Column1Block0,dataT24Column2Block0]
    · have rest : i.val-7 < 1048569 := by have := i.isLt; omega
      have index : i.val ≥ 7 := by omega
      have reference : wordROMValue i.val = #v[4211,49152] := by
        match h : i.val with
        | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
        | n+7 => rfl
      rw [reference]
      constructor
      · change getFromBlocks [.dense #[32947,33043,32819,29111,21015,41347,40995],.affine 1048569 4211 0] i.val = _
        rw [getFromBlocks]
        simp only [Block.length]
        simp only [show (#[32947,33043,32819,29111,21015,41347,40995] : Array Nat).size = 7 from rfl]
        rw [if_neg first,getFromBlocks]
        simp only [Block.length]
        rw [if_pos rest]
        simpa using affine_get 1048569 4211 0 (i.val-7) rest
      · change getFromBlocks [.dense #[16,65520,16416,0,0,0,32],.affine 1048569 49152 0] i.val = _
        rw [getFromBlocks]
        simp only [Block.length]
        simp only [show (#[16,65520,16416,0,0,0,32] : Array Nat).size = 7 from rfl]
        rw [if_neg first,getFromBlocks]
        simp only [Block.length]
        rw [if_pos rest]
        simpa using affine_get 1048569 49152 0 (i.val-7) rest
  have tag : dataT24.columns[3].get? i.val = some 24 := by
    change (⟨#[.affine 1048576 24 0]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 1048576 24 0 i.val i.isLt
  apply Vector.ext
  intro lane bound
  interval_cases lane <;> simp [TableData.rowNat,wordROMRow,key,value.1,value.2,tag]

end Airbender.ReducedMachine.NativeWordMemoryTableProofs
