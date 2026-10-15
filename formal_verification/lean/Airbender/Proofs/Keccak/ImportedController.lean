import Airbender.Review.Circuits.Keccak.Tables.Controller
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

namespace Airbender.Keccak.Controller.Proofs
open Setup
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/- Two six-bit coordinates cover every encoded control, keeping the kernel
   calculation shallow without restricting any active or fallback case. -/
private def splitKey (high low : Fin 64) : Fin 4096 :=
  ⟨64 * high.val + low.val, by have := high.isLt; have := low.isLt; omega⟩

private theorem splitKey_complete (key : Fin 4096) :
    ∃ high low : Fin 64, splitKey high low = key := by
  refine ⟨⟨key.val / 64, by have := key.isLt; omega⟩,
    ⟨key.val % 64, Nat.mod_lt _ (by decide)⟩, ?_⟩
  apply Fin.ext
  dsimp [splitKey]
  omega

private theorem reference_fields : ∀ lane : Fin 6, ∀ high low : Fin 64,
    (rows (splitKey high low))[lane] = (referenceRows (splitKey high low))[lane] := by
  intro lane
  fin_cases lane <;>
    dsimp only [rows, Vector.getElem_ofFn, Fin.getElem_fin, controllerData,
      Setup.Column.get?, Array.toList, splitKey, referenceRows]
  all_goals decide +kernel

/-- All 4,096 imported controls agree with the reference, including inactive
    and invalid-control fallback rows. -/
theorem rows_reference (key : Fin 4096) : rows key = referenceRows key := by
  obtain ⟨high, low, rfl⟩ := splitKey_complete key
  apply Vector.ext
  intro lane hLane
  exact reference_fields ⟨lane, hLane⟩ high low

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
private theorem rows_data_bound (key : Fin 4096) (lane : Fin 6) : (rows key)[lane] < 31 := by
  have good : ∀ block ∈ (controllerData.columns[lane.val + 1]).blocks.toList, blockBound block := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using blocks_bounded lane
  simpa only [rows, Fin.getElem_fin, Vector.getElem_ofFn, Column.get?] using get_bound _ good key.val
private theorem small_signed {n : Nat} (bound : n < 4096) : signedValue n = (n : Int) := by
  have small : n ≤ babyBearModulus / 2 := by dsimp [babyBearModulus]; omega
  unfold signedValue
  rw [if_pos small]
private theorem key_column (key : Fin 4096) :
    (controllerData.columns[0]).get? key.val = some key.val := by
  change getFromBlocks [.affine 4096 0 1] key.val = some key.val
  simp [getFromBlocks, Block.get?, Block.length, key.isLt]
private theorem tag_column (key : Fin 4096) :
    (controllerData.columns[7]).get? key.val = some 37 := by
  change getFromBlocks [.affine 4096 37 0] key.val = some 37
  simp [getFromBlocks, Block.get?, Block.length, key.isLt]
/-- The imported region binds the key, six outputs and native discriminator. -/
theorem controller_native_row (key : Fin 4096) : controllerData.row key =
    (#v[key.val, (rows key)[0], (rows key)[1], (rows key)[2], (rows key)[3],
      (rows key)[4], (rows key)[5], 37] : Vector Nat 8).map (fun (n : Nat) => (n : Int)) := by
  apply Vector.ext
  intro j hj
  simp only [TableData.row, Vector.getElem_map,
    show controllerData.offset = 0 from rfl, Nat.zero_add]
  interval_cases j
  · change signedValue (((controllerData.columns[0]).get? key.val).getD 0) = (key.val : Int)
    rw [key_column]
    exact small_signed key.isLt
  · have result := small_signed (lt_trans (rows_data_bound key 0) (by decide))
    simpa [rows] using result
  · have result := small_signed (lt_trans (rows_data_bound key 1) (by decide))
    simpa [rows] using result
  · have result := small_signed (lt_trans (rows_data_bound key 2) (by decide))
    simpa [rows] using result
  · have result := small_signed (lt_trans (rows_data_bound key 3) (by decide))
    simpa [rows] using result
  · have result := small_signed (lt_trans (rows_data_bound key 4) (by decide))
    simpa [rows] using result
  · have result := small_signed (lt_trans (rows_data_bound key 5) (by decide))
    simpa [rows] using result
  · change signedValue (((controllerData.columns[7]).get? key.val).getD 0) = (37 : Int)
    rw [tag_column]
    exact small_signed (by decide : 37 < 4096)

private def controllerIndex (key : Fin 4096) : Fin 1249281 :=
  ⟨controllerDataRegion.offset + key.val, by
    change 65537 + key.val < 1249281
    have size := key.isLt
    omega⟩

/-- The concrete lookup consumer uses exactly the imported native controller
    row at the exported region offset. -/
theorem controller_setup_row (key : Fin 4096) :
    (setupRow rows (controllerIndex key)).map (fun (n : Nat) => (n : Int)) =
      controllerData.row key := by
  rw [controller_native_row]
  congr 1
  unfold setupRow controllerIndex
  dsimp only [controllerDataRegion]
  have size := key.isLt
  split_ifs <;> try omega
  simp only [Nat.add_sub_cancel_left]

end Airbender.Keccak.Controller.Proofs
