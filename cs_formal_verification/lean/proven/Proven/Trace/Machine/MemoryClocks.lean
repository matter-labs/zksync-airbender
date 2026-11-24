module
public import Proven.Trace.Machine.UnifiedRequests
public import Proven.Trace.Machine.MemoryWorkers
public import Proven.Delegation.MixedClocks
public import Proven.UnifiedReduced.RVCaller.MixedMemoryClocks

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- One architectural transfer pool for the unrolled CPU and both worker pools. -/
def unrolledMemory (trace : PooledTrace babyBearModulus) (workers : WorkerPools babyBearModulus) : Transfer.Data babyBearModulus :=
  ⟨trace.initialMemory, trace.terminalMemory, unrolledSteps trace ++ workers.steps⟩

/-- One architectural transfer pool for the unified CPU and both worker pools. -/
def unifiedMemory (trace : UnifiedTrace babyBearModulus) (workers : WorkerPools babyBearModulus) : Transfer.Data babyBearModulus :=
  ⟨trace.initialMemory, trace.terminalMemory, unifiedSteps trace ++ workers.steps⟩

/-- Unrolled CPU and worker constraints bound every architectural write clock. -/
theorem unrolled_write_clocks {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    ∀ edge ∈ (unrolledMemory trace workers).steps, (timeOfPair edge.2.time).Bounded := by
  have clocks := state_clock_inputs (by decide : 2 * timestampBase + 4 < babyBearModulus)
    (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1)
    accepted.constraints accepted.states initial aligned
  intro edge present
  rcases List.mem_append.mp present with machine | worker
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have native := Delegation.Caller.Proofs.machine_port_native row (by simpa using portMember)
    have clock := clocks row member
    exact (write_time (by decide : timestampBase < babyBearModulus)
      (base := rawPair row.assignment row.columns.initialTime) clock.1 clock.2
      (Trace.Proofs.port_offset row port native)).1
  · exact worker_write_clocks (unrolled_worker_clocks accepted initial aligned).1 edge worker

/-- Unified CPU and worker constraints bound every architectural write clock. -/
theorem unified_write_clocks {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    ∀ edge ∈ (unifiedMemory trace workers).steps, (timeOfPair edge.2.time).Bounded := by
  have clocks := state_clock_inputs (by decide : 2 * timestampBase + 4 < babyBearModulus)
    (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1)
    accepted.constraints accepted.states initial aligned
  intro edge present
  rcases List.mem_append.mp present with machine | worker
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    have native := UnifiedReduced.Caller.Proofs.rv_machine_port_native row (by simpa using portMember)
    have clock := clocks row member
    exact (write_time (by decide : timestampBase < babyBearModulus)
      (base := rawPair row.assignment row.columns.initialTime) clock.1 clock.2
      (Trace.Proofs.port_offset row port native)).1
  · exact worker_write_clocks (unified_worker_clocks accepted initial aligned).1 edge worker

/-- Complete memory matching transports canonical clocks from seeds and writes to all reads. -/
theorem shared_memory_clocks {data : Transfer.Data babyBearModulus}
    (matching : (data.initial ++ data.steps.map Prod.snd).Perm (data.terminal ++ data.steps.map Prod.fst))
    (initial : ∀ token ∈ data.initial, (timeOfPair token.time).Bounded)
    (writes : ∀ edge ∈ data.steps, (timeOfPair edge.2.time).Bounded) :
    ∀ edge ∈ data.steps, (timeOfPair edge.1.time).Bounded ∧ (timeOfPair edge.2.time).Bounded := by
  have produced : ∀ token ∈ data.initial ++ data.steps.map Prod.snd, (timeOfPair token.time).Bounded := by
    intro token member
    rcases List.mem_append.mp member with seed | written
    · exact initial token seed
    · obtain ⟨edge, present, rfl⟩ := List.mem_map.mp written
      exact writes edge present
  intro edge member
  exact ⟨produced edge.1 (matching.mem_iff.mpr
    (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩)))), writes edge member⟩

/-- The encoded native write clock is the event clock used by the existing row rules. -/
theorem native_row_write_time {Kind : Type} [CircuitLayout Kind] [ClockLaws Kind babyBearModulus]
    {row : Trace.Row babyBearModulus Kind}
    (clock : (decodeTimestamp row.assignment row.columns.initialTime).Bounded ∧
      (decodeTimestamp row.assignment row.columns.initialTime).lo % 4 = 0)
    {port : MemoryPort} (present : port ∈ row.ports) :
    (timeOfPair (writeToken row.columns row.assignment port).time).value =
      (port.event row.columns row.assignment).1 :=
  (write_time (by decide : timestampBase < babyBearModulus)
    (base := rawPair row.assignment row.columns.initialTime) clock.1 clock.2
    (Trace.Proofs.port_offset row port present)).2

end Airbender.Trace.Machine.Proofs
