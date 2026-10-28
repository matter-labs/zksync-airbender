import Airbender.Review.Trace.Workers.Keccak.SplitSchedule

namespace Airbender.Keccak.Split.Proofs
open Airbender.Keccak.Split
set_option maxRecDepth 8192

theorem roundPattern_length : roundPattern.length = 15 := by decide
theorem schedule_length : schedule.length = 361 := by decide
theorem parity_calls : schedule.count .columnParity = 121 := by decide
theorem theta_rho_calls : schedule.count .thetaRho = 120 := by decide
theorem chi5_calls : schedule.count .chi5 = 120 := by decide

theorem csr_ne_external (kind : Kind) : kind.csr ≠ 0x7C0 := by
  cases kind <;> decide

theorem csr_ne_special5 (kind : Kind) : kind.csr ≠ 0x7CB := by
  cases kind <;> decide

/-- The finite call schedule agrees with the public CSR selector and progresses
from the blessed initial control to the final delayed-iota control. -/
theorem schedule_kind :
    ∀ index : Fin 361, schedule[index.val]? = some (kindAt index.val) := by
  decide

theorem initial_control : controlAt 0 = 0 := by decide
theorem final_call_control : controlAt 360 = 1536 := by decide
theorem final_control : bump (controlAt 360) = 1544 := by decide

theorem control_progression :
    ∀ index : Fin 360, bump (controlAt index.val) = controlAt (index.val + 1) := by
  decide

end Airbender.Keccak.Split.Proofs
