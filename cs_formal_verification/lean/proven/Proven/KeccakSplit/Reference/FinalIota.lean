module
public import Proven.KeccakSplit.Reference.CallSteps
public import Proven.Keccak.LayoutReduction
public import Batteries.Data.Fin.Fold

@[expose] public section

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true

/-- Call 360 applies the last original iota constant to the final lane layout. -/
theorem final_iota_reference (state : LaneState) :
    logicalLanes 24 (microStep 360 state) =
      iota (logicalLanes 24 state) roundConstants[23] := by
  apply Vector.ext
  intro lane bound
  have shape : (360 : Fin 361).val = 15 * 24 + 0 := rfl
  simp only [iota, Vector.getElem_set, logical_lanes_entry]
  by_cases first : lane < 5
  · rw [parity_step_lane shape (by decide) (by decide) state first (by simp only; omega)]
    by_cases zero : lane = 0
    · subst zero
      simp only [↓reduceIte, roundConstant]
      rfl
    · simp only [zero, ↓reduceIte, eq_comm (a := 0)]
  · rw [parity_step_kept shape (by decide) (by decide) state _
      (fun j position same => by rw [lane_slot_eq_iff, Fin.mk.injEq] at same; omega)
      (fun same => by
        have := lane_slot_bound 24 ⟨lane, bound⟩
        rw [← same] at this
        simp only at this
        omega)]
    simp only [show ¬ (0 = lane) by omega, ↓reduceIte]

/-- The twenty-four Pi renamings return to the original logical lane layout. -/
theorem logical_final_layout (state : LaneState) : logicalLanes 24 state = logicalLanes 0 state := by
  apply Vector.ext
  intro lane bound
  simp only [logicalLanes, Vector.getElem_ofFn, Airbender.Keccak.Proofs.physical_cached]
  rfl

end Airbender.Keccak.Split.Call.Proofs
