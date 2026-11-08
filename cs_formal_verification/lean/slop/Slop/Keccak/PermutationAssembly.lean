module
public import Slop.Keccak.RoundTrace
public import Slop.Keccak.Phases.Chi
public import Slop.Keccak.Phases.Iota
public import Slop.Keccak.Phases.Mix
public import Slop.Keccak.Phases.Rho
public import Slop.Keccak.Phases.Theta

@[expose] public section

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536

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

/-- Call 648 applies the last original iota constant to the final lane layout. -/
theorem final_iota_reference (state : LaneState) :
    logicalLanes 24 (microStep 648 state) = iota (logicalLanes 24 state) roundConstants[23] := by
  apply Vector.ext
  intro lane bound
  have shape : (648 : Fin 649).val = 27 * 24 + 0 := rfl
  simp only [iota, Vector.getElem_set, logical_lanes_entry]
  by_cases first : lane < 5
  · rw [iota_step_lane shape (by decide) state first (by simp only; omega)]
    by_cases zero : lane = 0
    · subst zero
      simp only [↓reduceIte]
      rfl
    · simp only [zero, false_and, ↓reduceIte, eq_comm (a := 0)]
  · rw [iota_step_kept shape (by decide) state _
      (fun j position same => by rw [physical_cell_eq_iff, Fin.mk.injEq] at same; omega)
      (fun same => by
        have := physical_cell_bound 24 ⟨lane, bound⟩
        rw [← same] at this
        simp only at this
        omega)]
    simp only [show ¬ (0 = lane) by omega, ↓reduceIte]

theorem final_layout (state : LaneState) : logicalLanes 24 state = logicalLanes 0 state := by
  apply Vector.ext
  intro i bound
  have finite : ∀ lane : Fin 25, Controller.physicalLane 24 lane = Controller.physicalLane 0 lane := by
    decide +kernel
  simp only [logicalLanes, Vector.getElem_ofFn, finite]

end Airbender.Keccak.Proofs
