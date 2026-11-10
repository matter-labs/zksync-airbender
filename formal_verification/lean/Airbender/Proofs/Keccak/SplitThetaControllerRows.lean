import Airbender.Data.Setup.Keccak.ThetaRhoSlots
import Airbender.Proofs.Keccak.SplitControlSetup
import Airbender.Proofs.Keccak.SplitSlotReduction

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000

/-- Exact native controller-row order for the five theta/rho calls of each round. -/
def thetaRhoControllerIndex (i : Fin thetaRhoControl.length) : Fin 361 :=
  ⟨15 * ((i.val - 1) / 5) + 5 + (i.val - 1) % 5, by
    have bound := i.isLt
    change i.val < 121 at bound
    omega⟩

/-- The actual controller pins the original control transition and all five column flags. -/
theorem theta_rho_controller_schedule : ∀ i : Fin thetaRhoControl.length,
    (thetaRhoControl.row i)[1] = 1 →
      kindAt (thetaRhoControllerIndex i).val = .thetaRho ∧
      (thetaRhoControl.row i)[0] = (controlAt (thetaRhoControllerIndex i).val : Int) ∧
      (thetaRhoControl.row i)[2] = (bump (controlAt (thetaRhoControllerIndex i).val) : Int) ∧
      (∀ column : Fin 5, (thetaRhoControl.row i)[3 + column.val] =
        if column.val = (thetaRhoControllerIndex i).val % 5 then 1 else 0) := by
  decide +kernel

/-- The actual slot table pins all five state lanes and both neighboring parity lanes. -/
theorem theta_rho_controller_slots : ∀ i : Fin thetaRhoControl.length,
    (thetaRhoControl.row i)[1] = 1 →
      let slotRow := thetaRhoSlots.row ⟨i.val, by have := i.isLt; exact this⟩
      slotRow[0] = ((controlAt (thetaRhoControllerIndex i).val + 2048 : Nat) : Int) ∧
      ∀ lane : Fin 7, slotRow[1 + lane.val] =
        ((Call.slots (thetaRhoControllerIndex i))[lane.val].val : Int) := by
  simp only [Call.Proofs.slots_normalized]
  decide +kernel

/-- Both exact native regions retain the same complete setup source. -/
theorem theta_rho_slots_source : thetaRhoSlotsSourceBytes = thetaRhoControlSourceBytes := by rfl

end Airbender.Keccak.Split.Native.Fixed.Proofs
