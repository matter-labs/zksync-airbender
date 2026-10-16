import Airbender.Proofs.Keccak.ControllerBounds
import Mathlib.Tactic.IntervalCases

namespace Airbender.Keccak.Controller.Proofs
open Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

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
private theorem row_signed_eq_nat {width : Nat} (data : TableData width)
    (key : Fin data.length) (offset : data.offset = 0)
    (bounded : ∀ (j : Nat) (hj : j < width), ((data.columns[j]).get? key.val).getD 0 < 4096) :
    data.row key = (data.columns.map (fun column => (column.get? key.val).getD 0)).map
      (fun n : Nat => (n : Int)) := by
  apply Vector.ext
  intro j hj
  simp only [TableData.row, Vector.getElem_map, offset, Nat.zero_add]
  exact small_signed (bounded j hj)

private theorem nat_row_of_columns (columns : Vector Column 8) (key : Nat)
    (outputs : Vector Nat 6)
    (first : (columns[0].get? key).getD 0 = key)
    (last : (columns[7].get? key).getD 0 = 37)
    (middle : ∀ j : Fin 6, (columns[j.val + 1].get? key).getD 0 = outputs[j]) :
    columns.map (fun column => (column.get? key).getD 0) =
      #v[key, outputs[0], outputs[1], outputs[2], outputs[3], outputs[4], outputs[5], 37] := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  · exact first
  · exact middle ⟨0, by decide⟩
  · exact middle ⟨1, by decide⟩
  · exact middle ⟨2, by decide⟩
  · exact middle ⟨3, by decide⟩
  · exact middle ⟨4, by decide⟩
  · exact middle ⟨5, by decide⟩
  · exact last

private theorem controller_nat_row (key : Fin 4096) :
    controllerData.columns.map (fun column => (column.get? key.val).getD 0) =
      (#v[key.val, (rows key)[0], (rows key)[1], (rows key)[2], (rows key)[3],
        (rows key)[4], (rows key)[5], 37] : Vector Nat 8) := by
  apply nat_row_of_columns controllerData.columns key.val (rows key)
  · simp only [key_column key, Option.getD_some]
  · simp only [tag_column key, Option.getD_some]
  · intro j
    simp only [rows, Fin.getElem_fin, Vector.getElem_ofFn]

private theorem columns_bounded (key : Fin 4096) :
    ∀ j : Fin 8, ((controllerData.columns[j]).get? key.val).getD 0 < 4096 := by
  intro j
  fin_cases j
  all_goals simp only [Fin.getElem_fin]
  · simpa only [key_column key, Option.getD_some] using key.isLt
  · simpa only [rows, Fin.getElem_fin, Vector.getElem_ofFn] using
      (lt_trans (rows_data_bound key (⟨0, by decide⟩ : Fin 6)) (by decide : 31 < 4096))
  · simpa only [rows, Fin.getElem_fin, Vector.getElem_ofFn] using
      (lt_trans (rows_data_bound key (⟨1, by decide⟩ : Fin 6)) (by decide : 31 < 4096))
  · simpa only [rows, Fin.getElem_fin, Vector.getElem_ofFn] using
      (lt_trans (rows_data_bound key (⟨2, by decide⟩ : Fin 6)) (by decide : 31 < 4096))
  · simpa only [rows, Fin.getElem_fin, Vector.getElem_ofFn] using
      (lt_trans (rows_data_bound key (⟨3, by decide⟩ : Fin 6)) (by decide : 31 < 4096))
  · simpa only [rows, Fin.getElem_fin, Vector.getElem_ofFn] using
      (lt_trans (rows_data_bound key (⟨4, by decide⟩ : Fin 6)) (by decide : 31 < 4096))
  · simpa only [rows, Fin.getElem_fin, Vector.getElem_ofFn] using
      (lt_trans (rows_data_bound key (⟨5, by decide⟩ : Fin 6)) (by decide : 31 < 4096))
  · simp only [tag_column key, Option.getD_some]
    decide

/-- The imported region binds the key, six outputs and native discriminator. -/
theorem controller_native_row (key : Fin 4096) : controllerData.row key =
    (#v[key.val, (rows key)[0], (rows key)[1], (rows key)[2], (rows key)[3],
      (rows key)[4], (rows key)[5], 37] : Vector Nat 8).map (fun (n : Nat) => (n : Int)) := by
  have bounded : ∀ (j : Nat) (hj : j < 8),
      ((controllerData.columns[j]).get? key.val).getD 0 < 4096 := by
    intro j hj
    simpa only [Fin.getElem_fin] using columns_bounded key ⟨j, hj⟩
  exact (row_signed_eq_nat controllerData key rfl bounded).trans
    (congrArg (Vector.map (fun n : Nat => (n : Int))) (controller_nat_row key))

end Airbender.Keccak.Controller.Proofs
