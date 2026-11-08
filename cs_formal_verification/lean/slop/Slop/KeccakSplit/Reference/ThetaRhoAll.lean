module
public import Slop.KeccakSplit.Reference.CallSteps
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true

/-- Clean's `rhoPi` reads lane `piSource lane` and rotates it by that lane's rho offset. -/
theorem rho_pi_entry (v : Vector Nat 25) (lane : Fin 25) :
    (rhoPi v)[lane.val] = rotLeft64 v[(Controller.piSource lane).val]
      ((rotations[(Controller.piSource lane).val / 5]'(by
        have := (Controller.piSource lane).isLt; omega))[(Controller.piSource lane).val % 5]'(by
          omega)) := by
  fin_cases lane <;> rfl

theorem theta_d_entry (c : Vector Nat 5) (column : Nat) (small : column < 5) :
    (thetaD c)[column] =
      c[(column + 4) % 5]'(by omega) ^^^ rotLeft64 (c[(column + 1) % 5]'(by omega)) 1 := by
  interval_cases column <;> rfl

/-- The theta+rho calls of any round give each lane rho of (lane ^ D[column]). -/
theorem theta_rho_phase_slot (round : Fin 24) (state : LaneState) (lane : Fin 25) :
    thetaRhoPhase round state (laneSlot round.val lane) =
      rotLeft64 (state (laneSlot round.val lane) ^^^
        (state ⟨25 + (lane.val / 5 + 4) % 5, by omega⟩ ^^^
          rotLeft64 (state ⟨25 + (lane.val / 5 + 1) % 5, by omega⟩) 1))
        ((rotations[lane.val / 5]'(by omega))[lane.val % 5]'(by omega)) := by
  have column : lane.val / 5 < 5 := by omega
  have position : lane.val % 5 < 5 := Nat.mod_lt _ (by decide)
  have split : lane.val = 5 * (lane.val / 5) + lane.val % 5 := by omega
  let owner : Fin 361 := ⟨15 * round.val + 5 + lane.val / 5, by omega⟩
  have shape : owner.val = 15 * round.val + 5 + lane.val / 5 := rfl
  let reads : Fin 31 → Prop := fun q =>
    (∃ j, ∃ _ : j < 5, laneSlot round.val ⟨5 * (lane.val / 5) + j, by omega⟩ = q) ∨ 25 ≤ q.val
  have here : reads (laneSlot round.val lane) :=
    Or.inl ⟨lane.val % 5, position, by rw [lane_slot_eq_iff]; exact Fin.ext split.symm⟩
  have kept (call : Fin 5) (other : call.val ≠ lane.val / 5) (t : LaneState) (q : Fin 31)
      (read : reads q) :
      microStep ⟨15 * round.val + 5 + call.val, by omega⟩ t q = t q := by
    apply theta_rho_step_kept (round := round.val) (column := call.val) rfl round.isLt call.isLt
    intro j position same
    rcases read with ⟨k, small, rfl⟩ | high
    · rw [lane_slot_eq_iff, Fin.mk.injEq] at same
      omega
    · have := lane_slot_bound round.val ⟨5 * call.val + j, by omega⟩
      rw [same] at this
      omega
  have covered (j : Fin 7) : reads (slots owner)[j] := by
    obtain ⟨j, bound⟩ := j
    rw [Fin.getElem_fin]
    by_cases low : j < 5
    · rw [theta_rho_slot_lane shape round.isLt column j low]
      exact Or.inl ⟨j, low, rfl⟩
    · right
      obtain rfl | rfl : j = 5 ∨ j = 6 := by omega
      · rw [theta_rho_slot_five shape round.isLt column]
        exact Nat.le_add_right 25 _
      · rw [theta_rho_slot_six shape round.isLt column]
        exact Nat.le_add_right 25 _
  refine (fold_owned (fun call t => microStep ⟨15 * round.val + 5 + call.val, by omega⟩ t) state
    (laneSlot round.val lane) ⟨lane.val / 5, column⟩ reads
    (fun call other t => kept call (fun same => other (Fin.ext same)) t _ here)
    (fun call other t q read => kept call (fun same => other (Fin.ext same)) t q read)
    (fun t t' agree => micro_step_congr owner _ (fun j => agree _ (covered j)) (agree _ here))).trans ?_
  exact theta_rho_step_lane shape round.isLt column state position split

/-- All twenty-four theta+rho phases match the original Keccak reference. -/
theorem theta_rho_phase_reference (round : Fin 24) (state : LaneState) :
    logicalLanes (round.val + 1) (thetaRhoPhase round state) =
      rhoPi (thetaXor (logicalLanes round.val state)
        (thetaD (Vector.ofFn fun column : Fin 5 => state ⟨25 + column.val, by omega⟩))) := by
  apply Vector.ext
  intro lane bound
  have source := (Controller.piSource ⟨lane, bound⟩).isLt
  rw [rho_pi_entry _ ⟨lane, bound⟩, theta_xor_entry, theta_d_entry _ _ (by omega)]
  simp only [logicalLanes, Vector.getElem_ofFn]
  exact theta_rho_phase_slot round state (Controller.piSource ⟨lane, bound⟩)

end Airbender.Keccak.Split.Call.Proofs
