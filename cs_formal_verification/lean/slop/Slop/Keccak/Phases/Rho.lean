module
public import Slop.Keccak.PhaseSteps

@[expose] public section

/-! The five rho calls of any round, proven once: each rotates its column in place, so the Pi renaming
of the next round's layout gives Clean's `rhoPi`. -/

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true

/-- Clean's `rhoPi` reads lane `piSource lane` and rotates it by that lane's rho offset. -/
theorem rho_pi_entry (v : Vector Nat 25) (lane : Fin 25) :
    (rhoPi v)[lane.val] = rotLeft64 v[(Controller.piSource lane).val]
      ((rhoRotations[(Controller.piSource lane).val / 5]'(by
        have := (Controller.piSource lane).isLt; omega))[(Controller.piSource lane).val % 5]'(by
          omega)) := by
  fin_cases lane <;> rfl

/-- The slots one rho call reads: its column. -/
def rhoReads (round column : Nat) (small : column < 5) (q : Fin 31) : Prop :=
  ∃ k, ∃ _ : k < 5, physicalCell round ⟨5 * column + k, by omega⟩ = q

theorem rho_kept (round : Fin 24) (column : Nat) (small : column < 5) (call : Fin 5)
    (other : call.val ≠ column) (t : LaneState) (q : Fin 31) (read : rhoReads round.val column small q) :
    microStep ⟨27 * round.val + 12 + call.val, by omega⟩ t q = t q := by
  apply rho_step_kept (round := round.val) (column := call.val) rfl call.isLt
  intro j position same
  obtain ⟨k, bound, rfl⟩ := read
  rw [physical_cell_eq_iff, Fin.mk.injEq] at same
  omega

/-- The rho calls of any round rotate every lane by its offset. -/
theorem rho_phase_slot (round : Fin 24) (state : LaneState) (lane : Fin 25) :
    rhoPhase round state (physicalCell round.val lane) =
      rotLeft64 (state (physicalCell round.val lane))
        ((rhoRotations[lane.val / 5]'(by omega))[lane.val % 5]'(Nat.mod_lt _ (by decide))) := by
  have column : lane.val / 5 < 5 := by omega
  have position : lane.val % 5 < 5 := Nat.mod_lt _ (by decide)
  have split : lane.val = 5 * (lane.val / 5) + lane.val % 5 := by omega
  have here : rhoReads round.val (lane.val / 5) column (physicalCell round.val lane) :=
    ⟨lane.val % 5, position, by rw [physical_cell_eq_iff]; exact Fin.ext split.symm⟩
  refine (fold_owned (fun call t => microStep ⟨27 * round.val + 12 + call.val, by omega⟩ t) state
    (physicalCell round.val lane) ⟨lane.val / 5, column⟩ (rhoReads round.val (lane.val / 5) column)
    (fun call other t => rho_kept round _ column call (fun same => other (Fin.ext same)) t _ here)
    (fun call other t q read => rho_kept round _ column call (fun same => other (Fin.ext same)) t q read)
    (fun t t' agree => ?_)).trans ?_
  · rw [rho_step_lane (round := round.val) rfl column t position split,
      rho_step_lane (round := round.val) rfl column t' position split, agree _ here]
  · exact rho_step_lane (round := round.val) rfl column state position split

theorem rho_phase_lanes (round : Fin 24) (state : LaneState) :
    logicalLanes (round.val + 1) (rhoPhase round state) = rhoPi (logicalLanes round.val state) := by
  apply Vector.ext
  intro lane bound
  rw [rho_pi_entry _ ⟨lane, bound⟩]
  simp only [logical_lanes_entry]
  exact rho_phase_slot round state (Controller.piSource ⟨lane, bound⟩)

end Airbender.Keccak.Proofs
