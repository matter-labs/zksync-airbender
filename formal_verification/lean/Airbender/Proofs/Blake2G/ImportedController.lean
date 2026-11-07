import Airbender.Review.Circuits.Blake2G.Tables.Controller
import Mathlib.Tactic.IntervalCases

namespace Airbender.Blake2G.Control.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

private def key (high : Fin 16) (low : Fin 32) : Fin 512 :=
  ⟨32 * high.val + low.val, by have := high.isLt; have := low.isLt; omega⟩
private theorem reference : ∀ high : Fin 16, ∀ low : Fin 32,
    controllerRows (key high low) =
    (step ⟨⟨(key high low).val % 256, Nat.mod_lt _ (by decide)⟩,
      decide (256 ≤ (key high low).val)⟩).row := by
  dsimp only [controllerRows, Vector.getElem_ofFn, key, Fin.getElem_fin,
    controllerData, Setup.Column.get?]
  decide +kernel

private theorem native : ∀ high : Fin 16, ∀ low : Fin 32,
    controllerData.row (key high low) =
    (#v[(key high low).val, (controllerRows (key high low))[0], (controllerRows (key high low))[1],
      (controllerRows (key high low))[2], (controllerRows (key high low))[3],
      (controllerRows (key high low))[4], (controllerRows (key high low))[5],
      (controllerRows (key high low))[6], 28] : Vector Nat 9).map (fun (n : Nat) => (n : Int)) := by
  intro high low
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals dsimp only [controllerRows, Vector.getElem_ofFn, key, Fin.getElem_fin,
    controllerData, Setup.Column.get?, Setup.TableData.row, Vector.getElem_map]
  all_goals revert low high
  all_goals decide +kernel +revert

private theorem split_key (index : Fin 512) :
    key ⟨index.val / 32, by have := index.isLt; omega⟩
      ⟨index.val % 32, Nat.mod_lt _ (by decide)⟩ = index := by
  apply Fin.ext
  dsimp only [key]
  omega

theorem controller_rows_reference : ∀ index : Fin 512, controllerRows index =
    (step ⟨⟨index.val % 256, Nat.mod_lt _ (by decide)⟩, decide (256 ≤ index.val)⟩).row := by
  intro index
  have same := reference ⟨index.val / 32, by have := index.isLt; omega⟩
    ⟨index.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [split_key] using same

theorem controller_native_row : ∀ index : Fin 512, controllerData.row index =
    (#v[index.val, (controllerRows index)[0], (controllerRows index)[1], (controllerRows index)[2],
      (controllerRows index)[3], (controllerRows index)[4], (controllerRows index)[5],
      (controllerRows index)[6], 28] : Vector Nat 9).map (fun (n : Nat) => (n : Int)) := by
  intro index
  have same := native ⟨index.val / 32, by have := index.isLt; omega⟩
    ⟨index.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [split_key] using same

private def controllerIndex (key : Fin 512) : Fin 344896 :=
  ⟨controllerDataRegion.offset + key.val, by
    change 344384 + key.val < 344896
    have size := key.isLt
    omega⟩

/-- The concrete consumer's controller rows include exactly the imported key,
    seven outputs and native discriminator at the exported region offset. -/
theorem controller_setup_row (key : Fin 512) :
    (setupRow controllerRows (controllerIndex key)).map (fun (n : Nat) => (n : Int)) =
      controllerData.row key := by
  rw [controller_native_row]
  congr 1
  unfold setupRow controllerIndex
  dsimp only [xor8DataRegion, xor3DataRegion, xor4DataRegion, xor7DataRegion,
    xor9DataRegion, controllerDataRegion]
  have size := key.isLt
  split_ifs <;> try { change 344384 + key.val < _ at *; omega }
  simp only [Nat.add_sub_cancel_left]

end Airbender.Blake2G.Control.Proofs
