module
public import Mathlib.Data.List.OfFn
public import Slop.Delegation.NativeViews
public import Slop.Keccak.CallHistory
public import Slop.Keccak.CallPorts
import all Init.Data.Array.Basic -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)

@[expose] public section

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
