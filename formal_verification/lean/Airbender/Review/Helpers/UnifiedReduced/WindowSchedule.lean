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

/-- Public program addresses exclude ordinary instructions from a caller region
    and identify its full CSR family. No selected row or worker count is supplied. -/
structure ProgramCallerRegion [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (family : Delegation.Family) (lower upper : Nat) : Prop where
  /-- Ordinary public entries lie outside the region's PC/clock interval. -/
  ordinary : ∀ entry ∈ program, ¬
    (data.machine.initial.word.value + lower ≤ entry.pc.toNat + (timeOfPair data.machine.initial.timestamp).value ∧
      entry.pc.toNat + (timeOfPair data.machine.initial.timestamp).value < data.machine.initial.word.value + upper)
  /-- Public CSR entries in that interval select the intended family. -/
  callers : ∀ entry ∈ data.program,
    data.machine.initial.word.value + lower ≤ entry.pc.toNat + (timeOfPair data.machine.initial.timestamp).value ∧
      entry.pc.toNat + (timeOfPair data.machine.initial.timestamp).value < data.machine.initial.word.value + upper →
    entry.data.family = family

/-- Public program shape and native matching derive the caller/worker region. -/
structure ProgramCallerWindow [Fact p.Prime] (data : RequestTrace p)
    (family : Delegation.Family) (lower upper : Nat) : Prop extends CallerWindowSchedule data lower upper where
  /-- Exact requests and native slots come from the accepted global matching. -/
  requests : Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper
  /-- Every selected worker has the public region's decoded full CSR family. -/
  family : ∀ row ∈ data.workers.windowRows lower upper, row.family = family

end Airbender.UnifiedReduced.Caller
