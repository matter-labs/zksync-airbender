module
public import Slop.Keccak.PhaseSteps

@[expose] public section

/-! The five theta calls of any round, proven once: each xors D[column] into its column. -/

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true

/-- The slots one theta call reads: its column and the scratch slots. -/
def thetaReads (round column : Nat) (small : column < 5) (q : Fin 31) : Prop :=
  (∃ k, ∃ _ : k < 5, physicalCell round ⟨5 * column + k, by omega⟩ = q) ∨ 25 ≤ q.val

theorem theta_kept (round : Fin 24) (column : Nat) (small : column < 5) (call : Fin 5)
    (other : call.val ≠ column) (t : LaneState) (q : Fin 31) (read : thetaReads round.val column small q) :
    microStep ⟨27 * round.val + 7 + call.val, by omega⟩ t q = t q := by
  apply theta_step_kept (round := round.val) (column := call.val) rfl call.isLt
  intro j position same
  rcases read with ⟨k, bound, rfl⟩ | high
  · rw [physical_cell_eq_iff, Fin.mk.injEq] at same
    omega
  · have := physical_cell_bound round.val ⟨5 * call.val + j, by omega⟩
    rw [same] at this
    omega

/-- The theta calls of any round xor D[column] into every lane of the column. -/
theorem theta_phase_slot (round : Fin 24) (state : LaneState) (lane : Fin 25) :
    thetaPhase round state (physicalCell round.val lane) =
      state (physicalCell round.val lane) ^^^ state ⟨25 + (lane.val / 5 + 4) % 5, by omega⟩ := by
  have column : lane.val / 5 < 5 := by omega
  have position : lane.val % 5 < 5 := Nat.mod_lt _ (by decide)
  have split : lane.val = 5 * (lane.val / 5) + lane.val % 5 := by omega
  have here : thetaReads round.val (lane.val / 5) column (physicalCell round.val lane) :=
    Or.inl ⟨lane.val % 5, position, by rw [physical_cell_eq_iff]; exact Fin.ext split.symm⟩
  have scratch : thetaReads round.val (lane.val / 5) column ⟨25 + (lane.val / 5 + 4) % 5, by omega⟩ :=
    Or.inr (Nat.le_add_right 25 _)
  refine (fold_owned (fun call t => microStep ⟨27 * round.val + 7 + call.val, by omega⟩ t) state
    (physicalCell round.val lane) ⟨lane.val / 5, column⟩ (thetaReads round.val (lane.val / 5) column)
    (fun call other t => theta_kept round _ column call (fun same => other (Fin.ext same)) t _ here)
    (fun call other t q read => theta_kept round _ column call (fun same => other (Fin.ext same)) t q read)
    (fun t t' agree => ?_)).trans ?_
  · rw [theta_step_lane (round := round.val) rfl column t position split,
      theta_step_lane (round := round.val) rfl column t' position split, agree _ here, agree _ scratch]
  · exact theta_step_lane (round := round.val) rfl column state position split

theorem theta_phase_lanes (round : Fin 24) (state : LaneState) :
    logicalLanes round.val (thetaPhase round state) =
      thetaXor (logicalLanes round.val state)
        (Vector.ofFn fun i : Fin 5 => state ⟨25 + (i.val + 4) % 5,
          by have := Nat.mod_lt (i.val + 4) (by decide : 0 < 5); omega⟩) := by
  apply Vector.ext
  intro lane bound
  rw [theta_xor_entry _ _ ⟨lane, bound⟩]
  simp only [logical_lanes_entry, Vector.getElem_ofFn]
  exact theta_phase_slot round state ⟨lane, bound⟩

end Airbender.Keccak.Proofs
