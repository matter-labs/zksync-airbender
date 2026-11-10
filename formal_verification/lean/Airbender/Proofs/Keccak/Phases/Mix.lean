import Airbender.Proofs.Keccak.PhaseDefinitions
import Airbender.Proofs.Keccak.SlotReduction

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

theorem mix_phase_frame (round : Fin 24) (state : LaneState) (lane : Fin 25) :
    mixPhase round state ⟨lane.val, by omega⟩ = state ⟨lane.val, by omega⟩ := by
  simp only [mixPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  fin_cases round
  all_goals fin_cases lane
  all_goals simp only [micro_normalized]
  all_goals rfl'

theorem mix_phase_d (round : Fin 24) (state : LaneState) (column : Fin 5) :
    mixPhase round state ⟨25 + (column.val + 4) % 5, by have := Nat.mod_lt (column.val + 4) (by decide : 0 < 5); omega⟩ =
      (thetaD (Vector.ofFn fun i : Fin 5 => state ⟨25 + i.val, by omega⟩))[column] := by
  simp only [mixPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  fin_cases round
  all_goals fin_cases column
  all_goals simp only [micro_normalized]
  all_goals rfl'

end Airbender.Keccak.Proofs
