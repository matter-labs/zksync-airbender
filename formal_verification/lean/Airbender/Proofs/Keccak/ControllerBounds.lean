import Airbender.Review.Circuits.Keccak.Tables.Controller
import Mathlib.Tactic.FinCases

namespace Airbender.Keccak.Controller.Proofs
open Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/- Bounds follow from the imported constant/dense/periodic blocks. No column
   recipe or reference-output assumption supplies the signed-row connection. -/
private def blockBound : Block → Prop
  | .affine _ first step => step = 0 ∧ first < 31
  | .dense values => ∀ i : Fin values.size, values[i] < 31
  | .periodic _ stride values => stride = 0 ∧ ∀ i : Fin values.size, values[i] < 31
private instance (block : Block) : Decidable (blockBound block) := by
  cases block <;> dsimp only [blockBound] <;> infer_instance
private theorem block_get_bound (block : Block) (good : blockBound block) (n : Nat) :
    (block.get? n).getD 0 < 31 := by
  cases block with
  | affine length first step =>
    rcases good with ⟨rfl, bound⟩
    by_cases h : n < length
    · simpa [Block.get?, Block.length, h] using bound
    · simp [Block.get?, Block.length, h]
  | dense values =>
    by_cases h : n < values.size
    · simpa [Block.get?, Block.length, h] using good ⟨n, h⟩
    · simp [Block.get?, Block.length, h]
  | periodic count stride values =>
    rcases good with ⟨rfl, bound⟩
    by_cases h : n < count * values.size
    · have positive : 0 < values.size := by
        by_contra empty
        have empty : values.size = 0 := by omega
        simp [empty] at h
      have hm := Nat.mod_lt n positive
      simpa [Block.get?, Block.length, h, hm] using bound ⟨n % values.size, hm⟩
    · simp [Block.get?, Block.length, h]
private theorem get_bound (blocks : List Block) :
    (∀ block ∈ blocks, blockBound block) → ∀ n : Nat,
      (getFromBlocks blocks n).getD 0 < 31 := by
  induction blocks with
  | nil => intro good n; simp [getFromBlocks]
  | cons block rest ih =>
    intro good n
    have head := good block (by simp)
    have tail : ∀ b ∈ rest, blockBound b := fun b hb => good b (by simp [hb])
    by_cases h : n < block.length
    · simpa [getFromBlocks, h] using block_get_bound block head n
    · simpa [getFromBlocks, h] using ih tail (n - block.length)
private theorem blocks_bounded : ∀ lane : Fin 6,
    (controllerData.columns[lane.val + 1]).blocks.toList.all (fun block => decide (blockBound block)) = true := by
  intro lane
  fin_cases lane <;> decide +kernel
theorem rows_data_bound (key : Fin 4096) (lane : Fin 6) : (rows key)[lane] < 31 := by
  have good : ∀ block ∈ (controllerData.columns[lane.val + 1]).blocks.toList, blockBound block := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using blocks_bounded lane
  simpa only [rows, Fin.getElem_fin, Vector.getElem_ofFn, Column.get?] using get_bound _ good key.val

end Airbender.Keccak.Controller.Proofs
