module
public import Slop.KeccakSplit.Reference.CallSteps
public import Slop.Keccak.ReferenceLemmas
public import Batteries.Data.Fin.Fold

@[expose] public section

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true

/-- The chi calls of any round give each lane its chi value along its row. -/
theorem chi_phase_slot (round : Fin 24) (state : LaneState) (lane : Fin 25) :
    chiPhase round state (laneSlot (round.val + 1) lane) =
      state (laneSlot (round.val + 1) lane) ^^^
        (not64 (state (laneSlot (round.val + 1) ⟨(lane.val + 5) % 25, by omega⟩)) &&&
          state (laneSlot (round.val + 1) ⟨(lane.val + 10) % 25, by omega⟩)) := by
  have row : lane.val % 5 < 5 := Nat.mod_lt _ (by decide)
  have position : (lane.val / 5 + 3 * (lane.val % 5)) % 5 < 5 := Nat.mod_lt _ (by decide)
  have split : lane.val =
      5 * (((lane.val / 5 + 3 * (lane.val % 5)) % 5 + 2 * (lane.val % 5)) % 5) + lane.val % 5 := by
    omega
  let owner : Fin 361 := ⟨15 * round.val + 10 + lane.val % 5, by omega⟩
  have shape : owner.val = 15 * round.val + 10 + lane.val % 5 := rfl
  let reads : Fin 31 → Prop := fun q =>
    (∃ k, ∃ _ : k < 5, laneSlot (round.val + 1) ⟨5 * k + lane.val % 5, by omega⟩ = q) ∨ 25 ≤ q.val
  have here : reads (laneSlot (round.val + 1) lane) :=
    Or.inl ⟨lane.val / 5, by omega, by rw [lane_slot_eq_iff]; exact Fin.ext (by simp only; omega)⟩
  have kept (call : Fin 5) (other : call.val ≠ lane.val % 5) (t : LaneState) (q : Fin 31)
      (read : reads q) :
      microStep ⟨15 * round.val + 10 + call.val, by omega⟩ t q = t q := by
    apply chi_step_kept (round := round.val) (row := call.val) rfl round.isLt call.isLt
    intro j position same
    rcases read with ⟨k, small, rfl⟩ | high
    · rw [lane_slot_eq_iff, Fin.mk.injEq] at same
      omega
    · have := lane_slot_bound (round.val + 1) ⟨5 * ((j + 2 * call.val) % 5) + call.val, by omega⟩
      rw [same] at this
      omega
  have covered (j : Fin 7) : reads (slots owner)[j] := by
    obtain ⟨j, bound⟩ := j
    rw [Fin.getElem_fin]
    by_cases low : j < 5
    · rw [chi_slot_lane shape round.isLt row j low]
      exact Or.inl ⟨(j + 2 * (lane.val % 5)) % 5, Nat.mod_lt _ (by decide), rfl⟩
    · right
      obtain rfl | rfl : j = 5 ∨ j = 6 := by omega
      · rw [chi_slot_five shape round.isLt row]
        decide
      · rw [chi_slot_six shape round.isLt row]
        decide
  refine (fold_owned (fun call t => microStep ⟨15 * round.val + 10 + call.val, by omega⟩ t) state
    (laneSlot (round.val + 1) lane) ⟨lane.val % 5, row⟩ reads
    (fun call other t => kept call (fun same => other (Fin.ext same)) t _ here)
    (fun call other t q read => kept call (fun same => other (Fin.ext same)) t q read)
    (fun t t' agree => micro_step_congr owner _ (fun j => agree _ (covered j)) (agree _ here))).trans ?_
  refine (chi_step_lane shape round.isLt row state position split).trans ?_
  congr <;> omega

/-- All twenty-four chi phases match the original Keccak reference. -/
theorem chi_phase_reference (round : Fin 24) (state : LaneState) :
    logicalLanes (round.val + 1) (chiPhase round state) =
      chi (logicalLanes (round.val + 1) state) := by
  apply Vector.ext
  intro lane bound
  rw [chi_entry _ ⟨lane, bound⟩]
  simp only [logical_lanes_entry]
  exact chi_phase_slot round state ⟨lane, bound⟩

end Airbender.Keccak.Split.Call.Proofs
