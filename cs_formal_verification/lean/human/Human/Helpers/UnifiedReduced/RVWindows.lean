import Human.Helpers.UnifiedReduced.RVMixedMemory
import Human.Helpers.Delegation.RVBoundaryMemory
import Human.Helpers.Delegation.WorkerProjection
import Human.Helpers.Delegation.RequestWindows

/-! RV siblings of `Windows.lean`, `WorkerProjection.lean` and `WindowProjection.lean` (helpers): native windows over
    `RVRequestTrace`, and cut images read from `RV.State`s (`Cell.readRV`). A RAM cell is RAM at any address, INCLUDING
    READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/

namespace Airbender.UnifiedReduced.Caller
open Trace

def RVRequestTrace.workerProjection [Fact p.Prime] (data : RVRequestTrace p) : Delegation.MemoryData p :=
  data.workers.workerProjection data.machine.initialMemory data.machine.terminalMemory

def RVRequestTrace.windowMachineRows [Fact p.Prime] (data : RVRequestTrace p) (lower upper : Nat) :=
  data.machine.rows.filter fun row => decide
    (lower ≤ Delegation.Caller.startClock row ∧ Delegation.Caller.startClock row < upper)

def RVRequestTrace.windowSteps [Fact p.Prime] (data : RVRequestTrace p) (lower upper : Nat) :=
  (data.windowMachineRows lower upper).flatMap (fun row => (machinePorts row).toList.map fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)) ++
    (data.workers.windowRows lower upper).flatMap Delegation.Row.memorySteps

def RVRequestTrace.prefixSteps [Fact p.Prime] (data : RVRequestTrace p) (cutoff : Nat) :=
  data.mixedSteps.filter fun edge => decide ((timeOfPair edge.2.time).value < cutoff)

/-- RV sibling of `NativeBoundary`: actual RV cell reads and canonical native tokens at a derived cut; raw timestamps
    are retained. -/
def RVNativeBoundary (tokens : List (MemoryToken p)) (state : RV.State) (cells : List Cell) : Prop :=
  Delegation.RVBoundaryImage tokens state cells ∧
    ∀ token ∈ tokens, token.word.Bounded ∧ (timeOfPair token.time).Bounded

def RVRequestTrace.windowProjection [Fact p.Prime] (data : RVRequestTrace p) (lower upper : Nat)
    (start finish : List (MemoryToken p)) : Delegation.MemoryData p :=
  ⟨data.workers.setup, data.workers.windowRows lower upper,
    start.filter fun token => token.address != (Cell.register 0).addressCode,
    finish.filter fun token => token.address != (Cell.register 0).addressCode⟩

def RVRequestTrace.prefixProjection [Fact p.Prime] (data : RVRequestTrace p) (lower : Nat)
    (start : List (MemoryToken p)) : Delegation.MemoryData p :=
  ⟨data.workers.setup, data.workers.prefixRows lower, data.workerProjection.initial,
    start.filter fun token => token.address != (Cell.register 0).addressCode⟩

/-- RV sibling of `CallerWindowSchedule`: clock matching and a public four-tick duration derive a caller-only region. -/
structure RVCallerWindowSchedule [Fact p.Prime] (data : RVRequestTrace p) (lower upper : Nat) : Prop where
  machineCount : (data.windowMachineRows lower upper).length = (upper - lower) / 4
  rows : Delegation.Caller.windowCallers data.callers lower upper = data.windowMachineRows lower upper
  workerCount : (data.windowMachineRows lower upper).length = (data.workers.windowRows lower upper).length

/-- RV sibling of `ProgramCallerRegion`: public RV program addresses exclude ordinary instructions from a caller region
    and identify its full CSR family. -/
structure RVProgramCallerRegion [Fact p.Prime] (data : RVRequestTrace p)
    (program : List UnifiedReduced.RVProgramEntry) (family : Delegation.Family) (lower upper : Nat) : Prop where
  ordinary : ∀ entry ∈ program, ¬
    (data.machine.initial.word.value + lower ≤ entry.pc.toNat + (timeOfPair data.machine.initial.timestamp).value ∧
      entry.pc.toNat + (timeOfPair data.machine.initial.timestamp).value < data.machine.initial.word.value + upper)
  callers : ∀ entry ∈ data.program,
    data.machine.initial.word.value + lower ≤ entry.pc.toNat + (timeOfPair data.machine.initial.timestamp).value ∧
      entry.pc.toNat + (timeOfPair data.machine.initial.timestamp).value < data.machine.initial.word.value + upper →
    entry.data.family = family

/-- RV sibling of `ProgramCallerWindow`. -/
structure RVProgramCallerWindow [Fact p.Prime] (data : RVRequestTrace p)
    (family : Delegation.Family) (lower upper : Nat) : Prop extends RVCallerWindowSchedule data lower upper where
  requests : Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper
  family : ∀ row ∈ data.workers.windowRows lower upper, row.family = family

end Airbender.UnifiedReduced.Caller
