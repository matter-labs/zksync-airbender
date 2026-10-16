import Airbender.Proofs.Keccak.ControllerNativeRow
import Airbender.Proofs.Keccak.ControllerBounds
import Airbender.Proofs.Keccak.ControllerCertificate0
import Airbender.Proofs.Keccak.ControllerCertificate1
import Airbender.Proofs.Keccak.ControllerCertificate2
import Airbender.Proofs.Keccak.ControllerCertificate3
import Airbender.Proofs.Keccak.ControllerCertificate4
import Airbender.Proofs.Keccak.ControllerCertificate5
import Airbender.Review.Circuits.Keccak.Tables.Controller
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

namespace Airbender.Keccak.Controller.Proofs
open Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Certificate

private theorem splitKey_complete (key : Fin 4096) :
    ∃ high low : Fin 64, splitKey high low = key := by
  refine ⟨⟨key.val / 64, by have := key.isLt; omega⟩,
    ⟨key.val % 64, Nat.mod_lt _ (by decide)⟩, ?_⟩
  apply Fin.ext
  dsimp [splitKey]
  omega

private theorem reference_fields (lane : Fin 6) (high low : Fin 64) :
    (rows (splitKey high low))[lane] = (referenceRows (splitKey high low))[lane] := by
  fin_cases lane
  · exact Certificate.field0 high low
  · exact Certificate.field1 high low
  · exact Certificate.field2 high low
  · exact Certificate.field3 high low
  · exact Certificate.field4 high low
  · exact Certificate.field5 high low

/-- All 4,096 imported controls agree with the reference, including inactive
    and invalid-control fallback rows. -/
theorem rows_reference (key : Fin 4096) : rows key = referenceRows key := by
  obtain ⟨high, low, rfl⟩ := splitKey_complete key
  apply Vector.ext
  intro lane hLane
  exact reference_fields ⟨lane, hLane⟩ high low

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
  dsimp only [controllerDataRegion, zeroDataRegion, xorDataRegion, iotaDataRegion,
    chiDataRegion, rotationDataRegion]
  have size := key.isLt
  split_ifs <;> try omega
  simp only [Nat.add_sub_cancel_left]

end Airbender.Keccak.Controller.Proofs
