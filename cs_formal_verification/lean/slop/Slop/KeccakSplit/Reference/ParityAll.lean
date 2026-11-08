module
public import Slop.KeccakSplit.Reference.CallSteps

@[expose] public section

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true

/-- The slots one parity call reads: its column, C[column] and the unused slot. -/
def parityReads (round column : Nat) (small : column < 5) (q : Fin 31) : Prop :=
  (∃ k, ∃ _ : k < 5, laneSlot round ⟨5 * column + k, by omega⟩ = q) ∨
    q = ⟨25 + column, by omega⟩ ∨ q.val = 30

theorem parity_kept (round : Fin 24) (column : Nat) (small : column < 5) (call : Fin 5)
    (other : call.val ≠ column) (t : LaneState) (q : Fin 31) (read : parityReads round.val column small q) :
    microStep ⟨15 * round.val + call.val, by omega⟩ t q = t q := by
  apply parity_step_kept (round := round.val) (column := call.val) rfl (by omega) call.isLt
  · intro j position same
    rcases read with ⟨k, bound, rfl⟩ | rfl | high
    · rw [lane_slot_eq_iff, Fin.mk.injEq] at same
      omega
    · have := lane_slot_bound round.val ⟨5 * call.val + j, by omega⟩
      rw [same] at this
      simp only at this
      omega
    · have := lane_slot_bound round.val ⟨5 * call.val + j, by omega⟩
      rw [same] at this
      omega
  · intro same
    rcases read with ⟨k, bound, rfl⟩ | rfl | high
    · have := lane_slot_bound round.val ⟨5 * column + k, by omega⟩
      rw [← same] at this
      simp only at this
      omega
    · rw [Fin.mk.injEq] at same
      omega
    · rw [← same] at high
      simp only at high
      omega

theorem parity_local (round : Fin 24) (column : Nat) (small : column < 5) (physical : Fin 31)
    (here : parityReads round.val column small physical) (t t' : LaneState)
    (agree : ∀ q, parityReads round.val column small q → t q = t' q) :
    microStep ⟨15 * round.val + column, by omega⟩ t physical =
      microStep ⟨15 * round.val + column, by omega⟩ t' physical := by
  have shape : (⟨15 * round.val + column, by omega⟩ : Fin 361).val = 15 * round.val + column := rfl
  apply micro_step_congr _ _ (fun j => agree _ ?_) (agree _ here)
  obtain ⟨j, bound⟩ := j
  rw [Fin.getElem_fin]
  by_cases low : j < 5
  · rw [parity_slot_lane shape (by omega) small j low]
    exact Or.inl ⟨j, low, rfl⟩
  · right
    obtain rfl | rfl : j = 5 ∨ j = 6 := by omega
    · rw [parity_slot_five shape (by omega) small]
      exact Or.inl rfl
    · rw [parity_slot_six shape (by omega) small]
      exact Or.inr rfl

/-- The parity calls of any round keep every lane, except the delayed iota on lane (0, 0). -/
theorem parity_phase_lane (round : Fin 24) (state : LaneState) (lane : Fin 25) :
    parityPhase round state (laneSlot round.val lane) =
      if lane.val = 0 then state (laneSlot round.val lane) ^^^ roundConstant round.val
      else state (laneSlot round.val lane) := by
  have column : lane.val / 5 < 5 := by omega
  have position : lane.val % 5 < 5 := Nat.mod_lt _ (by decide)
  have split : lane.val = 5 * (lane.val / 5) + lane.val % 5 := by omega
  have here : parityReads round.val (lane.val / 5) column (laneSlot round.val lane) :=
    Or.inl ⟨lane.val % 5, position, by rw [lane_slot_eq_iff]; exact Fin.ext split.symm⟩
  refine (fold_owned (fun call t => microStep ⟨15 * round.val + call.val, by omega⟩ t) state
    (laneSlot round.val lane) ⟨lane.val / 5, column⟩ (parityReads round.val (lane.val / 5) column)
    (fun call other t => parity_kept round _ column call (fun same => other (Fin.ext same)) t _ here)
    (fun call other t q read => parity_kept round _ column call (fun same => other (Fin.ext same)) t q read)
    (parity_local round _ column _ here)).trans ?_
  exact parity_step_lane (round := round.val) (column := lane.val / 5) rfl (by omega) column state
    position split

/-- The parity calls of any round write C[column] of the state after the delayed iota. -/
theorem parity_phase_column (round : Fin 24) (state : LaneState) (column : Fin 5) :
    parityPhase round state ⟨25 + column.val, by omega⟩ =
      (if column.val = 0 then
        state (laneSlot round.val ⟨5 * column.val, by omega⟩) ^^^ roundConstant round.val
      else state (laneSlot round.val ⟨5 * column.val, by omega⟩)) ^^^
        state (laneSlot round.val ⟨5 * column.val + 1, by omega⟩) ^^^
        state (laneSlot round.val ⟨5 * column.val + 2, by omega⟩) ^^^
        state (laneSlot round.val ⟨5 * column.val + 3, by omega⟩) ^^^
        state (laneSlot round.val ⟨5 * column.val + 4, by omega⟩) := by
  have here : parityReads round.val column.val column.isLt ⟨25 + column.val, by omega⟩ :=
    Or.inr (Or.inl rfl)
  refine (fold_owned (fun call t => microStep ⟨15 * round.val + call.val, by omega⟩ t) state
    ⟨25 + column.val, by omega⟩ column (parityReads round.val column.val column.isLt)
    (fun call other t => parity_kept round _ column.isLt call (fun same => other (Fin.ext same)) t _ here)
    (fun call other t q read =>
      parity_kept round _ column.isLt call (fun same => other (Fin.ext same)) t q read)
    (parity_local round _ column.isLt _ here)).trans ?_
  exact parity_step_column (round := round.val) (column := column.val) rfl (by omega) column.isLt state

/-- All 120 round parity calls match the original delayed-iota reference. -/
theorem parity_phase_reference (round : Fin 24) (state : LaneState) :
    logicalLanes round.val (parityPhase round state) =
      iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val) ∧
    (∀ column : Fin 5, parityPhase round state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val)))[column]) := by
  have lanes : logicalLanes round.val (parityPhase round state) =
      iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val) := by
    apply Vector.ext
    intro lane bound
    rw [logical_lanes_entry, parity_phase_lane]
    have small : round.val % 25 = round.val := Nat.mod_eq_of_lt (by omega)
    simp only [iotaState, Fin.val_ofNat, small]
    by_cases zero : round.val = 0
    · simp [zero, roundConstant, logical_lanes_entry]
    · have positive : 0 < round.val := by omega
      simp [positive, roundConstant, iota, Vector.getElem_set, logical_lanes_entry, eq_comm (a := 0),
        show round.val ≤ 24 by omega]
      by_cases first : lane = 0
      · subst first
        rfl
      · simp only [first, ↓reduceIte]
  refine ⟨lanes, fun column => ?_⟩
  rw [Fin.getElem_fin, theta_c_entry _ column.val column.isLt, ← lanes]
  simp only [logical_lanes_entry, parity_phase_lane, parity_phase_column]
  by_cases zero : column.val = 0 <;> simp [zero]

end Airbender.Keccak.Split.Call.Proofs
