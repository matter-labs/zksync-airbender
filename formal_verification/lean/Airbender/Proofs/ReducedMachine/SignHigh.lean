import Airbender.Review.Circuits.ReducedMachine.Tables.SignHighData
import Airbender.Proofs.Tables.PeriodicColumns
import Mathlib.Tactic.IntervalCases

namespace Airbender.ReducedMachine.SignHighProofs
open Setup Setup.Proofs SignHigh
set_option warningAsError true
set_option Elab.async false

private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

private theorem single_get (block : Block) (n : Nat) (bound : n < block.length) :
    (⟨#[block]⟩ : Column).get? n = block.get? n := by
  change getFromBlocks [block] n = _
  rw [getFromBlocks, if_pos bound]

/-- Every actual exported value is checked symbolically from its literal blocks. -/
theorem rows (i : Fin 65536) :
    data.rowNat i = #v[i.val, i.val / 32768, i.val / 256, 16] := by
  have key : data.columns[0].get? i.val = some i.val := by
    change (⟨#[.affine 65536 0 1]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 65536 0 1 i.val i.isLt
  have sign : data.columns[1].get? i.val = some (i.val / 32768) := by
    change getFromBlocks [.affine 32768 0 0, .affine 32768 1 0] i.val = _
    by_cases low : i.val < 32768
    · simp only [getFromBlocks, Block.length, if_pos low]
      simpa [Nat.div_eq_of_lt low] using affine_get 32768 0 0 i.val low
    · have rest : i.val - 32768 < 32768 := by omega
      have quotient : i.val / 32768 = 1 := by omega
      simp only [getFromBlocks, Block.length, if_neg low, if_pos rest]
      simpa [quotient] using affine_get 32768 1 0 (i.val - 32768) rest
  have highStored : data.columns[2].blocks =
      #[.periodic 256 1 (Array.replicate 256 0)] := by decide +kernel
  have high : data.columns[2].get? i.val = some (i.val / 256) := by
    rw [Column.get?, highStored]
    change getFromBlocks [.periodic 256 1 (Array.replicate 256 0)] i.val = _
    have inside : i.val < 256 * (Array.replicate 256 0).size := by
      simpa only [Array.size_replicate] using i.isLt
    rw [getFromBlocks, if_pos (show i.val <
      (Block.periodic 256 1 (Array.replicate 256 0)).length from inside)]
    simpa using periodic_get (Array.replicate 256 0) 256 1 i.val (by simp) inside
  have tag : data.columns[3].get? i.val = some 16 := by
    change (⟨#[.affine 65536 16 0]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 65536 16 0 i.val i.isLt
  ext lane bound
  interval_cases lane <;> simp [TableData.rowNat,key,sign,high,tag]

private theorem canonical (n : Nat) (bound : n < 65536) :
    (n : ZMod mersenne31Modulus).val = n := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by change n < 2147483647; omega)]

theorem result (query : Vector (ZMod mersenne31Modulus) 4)
    (member : Contains query) :
    query[0].val < 65536 ∧ query[1].val = query[0].val / 32768 ∧
      query[2].val = query[0].val / 256 ∧ query[3] = 16 := by
  obtain ⟨i,rfl⟩ := member
  have bound : i.val < 65536 := i.isLt
  have signBound : i.val / 32768 < 65536 := by omega
  have highBound : i.val / 256 < 65536 := by omega
  simp [TableData.row,rows,canonical _ bound,canonical _ signBound,canonical _ highBound]
  exact bound

end Airbender.ReducedMachine.SignHighProofs
