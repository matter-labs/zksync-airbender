import Airbender.Proofs.Keccak.SplitParityAll
import Airbender.Proofs.Keccak.SplitThetaRhoAll
import Airbender.Proofs.Keccak.SplitChiAll
import Airbender.Proofs.Keccak.RoundTrace

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true

def assembledRound (round : Fin 24) (state : LaneState) : LaneState :=
  chiPhase round (thetaRhoPhase round (parityPhase round state))

/-- Fifteen public split calls implement one original Keccak round with delayed iota. -/
theorem assembled_round_reference (round : Fin 24) (state : LaneState) :
    logicalLanes (round.val + 1) (assembledRound round state) =
      Airbender.Keccak.Proofs.roundBody
        (iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val)) := by
  have parities : (Vector.ofFn fun column : Fin 5 =>
      parityPhase round state ⟨25 + column.val, by omega⟩) =
      thetaC (iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val)) := by
    apply Vector.ext
    intro column bound
    simpa only [Vector.getElem_ofFn, Fin.getElem_fin] using
      (parity_phase_reference round state).2 ⟨column, bound⟩
  rw [assembledRound, chi_phase_reference, theta_rho_phase_reference,
    (parity_phase_reference round state).1, parities]
  rfl

end Airbender.Keccak.Split.Call.Proofs
