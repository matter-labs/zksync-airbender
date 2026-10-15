import Airbender.Review.Circuits.Blake2G.Tables.Controller

namespace Airbender.Blake2G.Control.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem controller_rows_reference : ∀ key : Fin 512, controllerRows key =
    (step ⟨⟨key.val % 256, Nat.mod_lt _ (by decide)⟩, decide (256 ≤ key.val)⟩).row := by
  decide +kernel

theorem controller_native_row : ∀ key : Fin 512, controllerData.row key =
    (#v[key.val, (controllerRows key)[0], (controllerRows key)[1], (controllerRows key)[2],
      (controllerRows key)[3], (controllerRows key)[4], (controllerRows key)[5],
      (controllerRows key)[6], 28] : Vector Nat 9).map (fun (n : Nat) => (n : Int)) := by
  decide +kernel

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
  dsimp only
  have size := key.isLt
  split_ifs <;> try { change 344384 + key.val < _ at *; omega }
  simp only [controllerDataRegion, Nat.add_sub_cancel_left]

end Airbender.Blake2G.Control.Proofs
