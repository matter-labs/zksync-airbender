import Airbender.Review.Helpers.UnifiedReduced.WindowProjection

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Clock matching and a public four-tick duration derive a caller-only region
    inside a mixed trace. Ordinary rows may occur before and after the cuts. -/
structure CallerWindowSchedule [Fact p.Prime] (data : RequestTrace p) (lower upper : Nat) : Prop where
  /-- Exact instruction count from accepted state matching and clock advancement. -/
  machineCount : (data.windowMachineRows lower upper).length = (upper - lower) / 4
  /-- Every selected machine row is an actual caller, in its native list order. -/
  rows : Delegation.Caller.windowCallers data.callers lower upper = data.windowMachineRows lower upper
  /-- Each selected caller has one selected worker; surplus workers stay outside. -/
  workerCount : (data.windowMachineRows lower upper).length = (data.workers.windowRows lower upper).length

end Airbender.UnifiedReduced.Caller
