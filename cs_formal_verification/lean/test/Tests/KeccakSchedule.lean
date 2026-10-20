import Slop.Keccak.Schedule

namespace Tests.KeccakSchedule
open Airbender.Keccak Airbender.Keccak.Proofs
set_option warningAsError true

theorem caller_endpoints : (scheduleControl 0).packed = 0 ∧
    (scheduleControl 649).packed = 1544 := ⟨schedule_start, schedule_finish⟩

theorem initial_parity : (scheduleControl 4).mode = 0 ∧
    (scheduleControl 4).iteration = 4 ∧ (scheduleControl 5).mode = 1 := by decide

theorem final_iota : (scheduleControl 648).mode = 0 ∧
    (scheduleControl 648).iteration = 0 ∧ (scheduleControl 648).round = 24 := by decide

theorem final_transition : (scheduleControl 648).nextPacked = 1544 := schedule_next 648

theorem completion_does_not_restart :
    (scheduleControl 649).packed ≠ (scheduleControl 0).packed ∧
      (scheduleControl 649).nextPacked = 1552 := by decide

end Tests.KeccakSchedule
