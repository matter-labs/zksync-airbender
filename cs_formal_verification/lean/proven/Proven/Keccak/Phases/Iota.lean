module
public import Proven.Keccak.PhaseSteps

@[expose] public section

/-! The five iota calls of any round, proven once: each gives its column the delayed round constant and
writes the column's parity. -/

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true

/-- The slots one iota call reads or writes: its column and C[column]. -/
def iotaReads (round column : Nat) (small : column < 5) (q : Fin 31) : Prop :=
  (∃ k, ∃ _ : k < 5, physicalCell round ⟨5 * column + k, by omega⟩ = q) ∨ q = ⟨25 + column, by omega⟩

theorem iota_kept (round : Fin 24) (column : Nat) (small : column < 5) (call : Fin 5)
    (other : call.val ≠ column) (t : LaneState) (q : Fin 31) (read : iotaReads round.val column small q) :
    microStep ⟨27 * round.val + call.val, by omega⟩ t q = t q := by
  apply iota_step_kept (round := round.val) (column := call.val) rfl call.isLt
  · intro j position same
    rcases read with ⟨k, bound, rfl⟩ | rfl
    · rw [physical_cell_eq_iff, Fin.mk.injEq] at same
      omega
    · have := physical_cell_bound round.val ⟨5 * call.val + j, by omega⟩
      rw [same] at this
      simp only at this
      omega
  · intro same
    rcases read with ⟨k, bound, rfl⟩ | rfl
    · have := physical_cell_bound round.val ⟨5 * column + k, by omega⟩
      rw [← same] at this
      simp only at this
      omega
    · rw [Fin.mk.injEq] at same
      omega

/-- The iota calls of any round keep every lane, except the delayed round constant on lane (0, 0). -/
theorem iota_phase_lane (round : Fin 24) (state : LaneState) (lane : Fin 25) :
    iotaPhase round state (physicalCell round.val lane) =
      if lane.val = 0 ∧ 0 < round.val then
        state (physicalCell round.val lane) ^^^ (roundConstants[Fin.ofNat 24 (round.val - 1)].toFin : Nat)
      else state (physicalCell round.val lane) := by
  have column : lane.val / 5 < 5 := by omega
  have position : lane.val % 5 < 5 := Nat.mod_lt _ (by decide)
  have split : lane.val = 5 * (lane.val / 5) + lane.val % 5 := by omega
  have here : iotaReads round.val (lane.val / 5) column (physicalCell round.val lane) :=
    Or.inl ⟨lane.val % 5, position, by rw [physical_cell_eq_iff]; exact Fin.ext split.symm⟩
  refine (fold_owned (fun call t => microStep ⟨27 * round.val + call.val, by omega⟩ t) state
    (physicalCell round.val lane) ⟨lane.val / 5, column⟩ (iotaReads round.val (lane.val / 5) column)
    (fun call other t => iota_kept round _ column call (fun same => other (Fin.ext same)) t _ here)
    (fun call other t q read => iota_kept round _ column call (fun same => other (Fin.ext same)) t q read)
    (fun t t' agree => ?_)).trans ?_
  · rw [iota_step_lane (round := round.val) rfl column t position split,
      iota_step_lane (round := round.val) rfl column t' position split, agree _ here]
  · exact iota_step_lane (round := round.val) rfl column state position split

/-- The iota calls of any round write C[column] of the state after the delayed round constant. -/
theorem iota_phase_parity (round : Fin 24) (state : LaneState) (column : Fin 5) :
    iotaPhase round state ⟨25 + column.val, by omega⟩ =
      (if column.val = 0 ∧ 0 < round.val then
        state (physicalCell round.val ⟨5 * column.val, by omega⟩) ^^^
          (roundConstants[Fin.ofNat 24 (round.val - 1)].toFin : Nat)
      else state (physicalCell round.val ⟨5 * column.val, by omega⟩)) ^^^
        state (physicalCell round.val ⟨5 * column.val + 1, by omega⟩) ^^^
        state (physicalCell round.val ⟨5 * column.val + 2, by omega⟩) ^^^
        state (physicalCell round.val ⟨5 * column.val + 3, by omega⟩) ^^^
        state (physicalCell round.val ⟨5 * column.val + 4, by omega⟩) := by
  have here : iotaReads round.val column.val column.isLt ⟨25 + column.val, by omega⟩ := Or.inr rfl
  have lane (k : Nat) (bound : k < 5) :
      iotaReads round.val column.val column.isLt (physicalCell round.val ⟨5 * column.val + k, by omega⟩) :=
    Or.inl ⟨k, bound, rfl⟩
  have lane0 : iotaReads round.val column.val column.isLt (physicalCell round.val ⟨5 * column.val, by omega⟩) :=
    Or.inl ⟨0, by decide, rfl⟩
  refine (fold_owned (fun call t => microStep ⟨27 * round.val + call.val, by omega⟩ t) state
    ⟨25 + column.val, by omega⟩ column (iotaReads round.val column.val column.isLt)
    (fun call other t => iota_kept round _ column.isLt call (fun same => other (Fin.ext same)) t _ here)
    (fun call other t q read =>
      iota_kept round _ column.isLt call (fun same => other (Fin.ext same)) t q read)
    (fun t t' agree => ?_)).trans ?_
  · rw [iota_step_parity (round := round.val) rfl column.isLt t,
      iota_step_parity (round := round.val) rfl column.isLt t', agree _ lane0,
      agree _ (lane 1 (by decide)), agree _ (lane 2 (by decide)), agree _ (lane 3 (by decide)),
      agree _ (lane 4 (by decide))]
  · exact iota_step_parity (round := round.val) rfl column.isLt state

theorem iota_phase_lanes (round : Fin 24) (state : LaneState) :
    logicalLanes round.val (iotaPhase round state) =
      iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val) := by
  apply Vector.ext
  intro lane bound
  rw [logical_lanes_entry, iota_phase_lane]
  have small : round.val % 25 = round.val := Nat.mod_eq_of_lt (by omega)
  simp only [iotaState, Fin.val_ofNat, small]
  by_cases zero : round.val = 0
  · simp only [zero, Nat.lt_irrefl, and_false, ↓reduceIte, dite_false, logical_lanes_entry]
  · have positive : 0 < round.val := by omega
    have index : roundConstants[Fin.ofNat 24 (round.val - 1)] = roundConstants[round.val - 1] := by
      simp only [Fin.getElem_fin, Fin.val_ofNat, Nat.mod_eq_of_lt (show round.val - 1 < 24 by omega)]
    simp only [positive, and_true, dite_true, iota, Vector.getElem_set, logical_lanes_entry, index]
    by_cases first : lane = 0
    · subst first
      simp only [↓reduceIte]
    · simp only [first, ↓reduceIte, show ¬ 0 = lane by omega]

theorem iota_phase_parities (round : Fin 24) (state : LaneState) (column : Fin 5) :
    iotaPhase round state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val)))[column] := by
  rw [Fin.getElem_fin, theta_c_entry _ column.val column.isLt, ← iota_phase_lanes]
  simp only [logical_lanes_entry, iota_phase_lane, iota_phase_parity]
  by_cases zero : column.val = 0 <;> simp [zero]

end Airbender.Keccak.Proofs
