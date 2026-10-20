import Slop.Keccak.PermutationPhases
import Slop.Keccak.RoundTrace

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000
set_option cbv.maxSteps 2000000
attribute [local cbv_opaque] rotLeft64 not64 Nat.xor Nat.land roundConstants

def assembledRound (round : Fin 24) (state : LaneState) : LaneState :=
  chiPhase round (rhoPhase round (thetaPhase round (mixPhase round (iotaPhase round state))))

theorem assembled_round_reference (round : Fin 24) (state : LaneState) :
    logicalLanes (round.val + 1) (assembledRound round state) =
      roundBody (iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val)) := by
  let prepared := iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val)
  have unchanged : logicalLanes round.val (mixPhase round (iotaPhase round state)) = prepared := by
    have frame : logicalLanes round.val (mixPhase round (iotaPhase round state)) =
        logicalLanes round.val (iotaPhase round state) := by
      apply Vector.ext
      intro lane bound
      simp only [logicalLanes, Vector.getElem_ofFn]
      exact mix_phase_frame round (iotaPhase round state)
        ⟨Controller.physicalLane round.val ⟨lane, bound⟩, Controller.Proofs.physical_bound _ _⟩
    exact frame.trans (iota_phase_lanes round state)
  have parity : (Vector.ofFn fun i : Fin 5 => iotaPhase round state ⟨25 + i.val, by omega⟩) = thetaC prepared := by
    apply Vector.ext
    intro i bound
    simpa only [Vector.getElem_ofFn, Fin.getElem_fin] using iota_phase_parities round state ⟨i, bound⟩
  have mixed : (Vector.ofFn fun i : Fin 5 =>
      mixPhase round (iotaPhase round state) ⟨25 + (i.val + 4) % 5,
        by have := Nat.mod_lt (i.val + 4) (by decide : 0 < 5); omega⟩) = thetaD (thetaC prepared) := by
    apply Vector.ext
    intro i bound
    have d := mix_phase_d round (iotaPhase round state) ⟨i, bound⟩
    rw [parity] at d
    simpa only [Vector.getElem_ofFn, Fin.getElem_fin] using d
  rw [assembledRound, chi_phase_lanes, rho_phase_lanes, theta_phase_lanes, unchanged, mixed]
  rfl

theorem final_iota_reference (state : LaneState) :
    logicalLanes 24 (microStep 648 state) = iota (logicalLanes 24 state) roundConstants[23] := by
  apply Vector.ext
  intro i bound
  simp only [logicalLanes, Vector.getElem_ofFn]
  interval_cases i
  all_goals simp only [physical_cached, micro_normalized]
  all_goals cbv

theorem final_layout (state : LaneState) : logicalLanes 24 state = logicalLanes 0 state := by
  apply Vector.ext
  intro i bound
  have finite : ∀ lane : Fin 25, Controller.physicalLane 24 lane = Controller.physicalLane 0 lane := by
    decide +kernel
  simp only [logicalLanes, Vector.getElem_ofFn, finite]

end Airbender.Keccak.Proofs
