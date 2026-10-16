import Airbender.Proofs.Keccak.ControllerLayout
import Airbender.Proofs.BabyBear

set_option Elab.async false

namespace Tests.KeccakController
open Airbender Keccak
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem initial_iota : Controller.rows ⟨2048, by decide⟩ = #v[0, 5, 10, 15, 20, 25] := by decide +kernel

theorem theta_physical_slots : Controller.rows ⟨2051, by decide⟩ = #v[0, 5, 10, 15, 20, 29] := by decide +kernel

theorem last_chi_slots : Controller.rows ⟨2054 + 32 + 64 * 23, by decide⟩ =
    #v[20, 23, 24, 25, 26, 27] := by decide +kernel

theorem round24_layout (lane : Fin 25) :
    Controller.physicalLane 24 lane = lane.val / 5 + 5 * (lane.val % 5) := by
  fin_cases lane <;> decide

theorem invalid_round_fallback : Controller.rows ⟨2051 + 64 * 24, by decide⟩ = #v[0, 1, 2, 3, 4, 5] := by decide +kernel

theorem padding_is_separate : Controller.rows ⟨0, by decide⟩ = Vector.replicate 6 0 ∧
    Controller.rows ⟨2048, by decide⟩ ≠ Vector.replicate 6 0 := by decide +kernel

end Tests.KeccakController
