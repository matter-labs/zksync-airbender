import Mathlib.Data.List.OfFn
import Slop.Delegation.NativeViews
import Slop.Keccak.CallHistory
import Slop.Keccak.CallPorts

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem scheduled_lane_coverage (physical : Fin 31) :
    ∃ call : Fin 649, ∃ lane : Fin 6,
      (Controller.rows (Fin.ofNat 4096 ((scheduleControl ⟨call.val, by omega⟩).packed + 2048)))[lane] = physical.val := by
  have all : ∀ physical : Fin 31, ∃ call : Fin 649, ∃ lane : Fin 6,
      (Controller.rows (Fin.ofNat 4096 ((scheduleControl ⟨call.val, by omega⟩).packed + 2048)))[lane] = physical.val := by
    decide +kernel
  exact all physical

end Airbender.Keccak.Proofs
