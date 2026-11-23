module
public import Human.Trace.Machine.Model
public import Proven.Delegation.NativeInvocation
public import Proven.KeccakSplit.NativeInvocation
public import Proven.Delegation.RequestTrace
public import Proven.Delegation.Requests
public import Proven.Trace.Pooled

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Delegation

/-- No active standard or split worker can cancel its own request with a zero clock. -/
theorem worker_fulfillments_live {workers : WorkerPools babyBearModulus}
    (accepted : WorkersAccepted workers) :
    ∀ request ∈ workers.fulfillments, Requests.Live request := by
  intro request member
  rcases List.mem_append.mp member with standard | split
  · obtain ⟨row, present, rfl⟩ := List.mem_map.mp standard
    exact Delegation.Proofs.active_invocation_live (accepted.standardConstraints row present)
      (accepted.standardActive row present)
  · obtain ⟨row, present, rfl⟩ := List.mem_map.mp split
    exact Keccak.Split.Native.Proofs.active_invocation_live (accepted.splitConstraints row present)
      (accepted.splitActive row present)

/-- Live request matching retains every caller and every worker occurrence. -/
theorem matching_permutation {calls fulfillments : List (Requests.Request p)}
    (matching : Requests.Matching calls fulfillments)
    (callLive : ∀ call ∈ calls, Requests.Live call)
    (workerLive : ∀ worker ∈ fulfillments, Requests.Live worker) : calls.Perm fulfillments := by
  have callsUnchanged : calls.filter (fun call => decide (Requests.Live call)) = calls :=
    List.filter_eq_self.mpr (fun call member => decide_eq_true (callLive call member))
  have workersUnchanged : fulfillments.filter (fun worker => decide (Requests.Live worker)) = fulfillments :=
    List.filter_eq_self.mpr (fun worker member => decide_eq_true (workerLive worker member))
  simpa only [callsUnchanged, workersUnchanged] using Delegation.Requests.Proofs.nonzero_matching matching

/-- A selected unrolled caller is an actual ADD/SUB row of the machine path. -/
theorem unrolled_caller_member [Fact p.Prime] {trace : PooledTrace p}
    {row : Trace.Row p PooledFamily} (member : row ∈ unrolledCallers trace) :
    row ∈ trace.rows ∧ row.family = .addSub := by
  obtain ⟨present, selected⟩ := List.mem_filter.mp member
  have family : row.family = .addSub := by cases equal : row.family <;> simp_all
  exact ⟨present, family⟩

/-- Initialized native CPU clocks make every issued caller request live and leave room for worker writes. -/
theorem unrolled_caller_clocks {trace : PooledTrace babyBearModulus}
    {workers : WorkerPools babyBearModulus} {program : List RVMachineProgramEntry}
    (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    ∀ row ∈ unrolledCallers trace,
      (timeOfPair (Requests.caller row.assignment).time).Bounded ∧
      Requests.Live (Requests.caller row.assignment) ∧
      (timeOfPair (Requests.caller row.assignment).time).lo + 2 < timestampBase := by
  have clocks := Trace.Proofs.state_clock_inputs (by decide : 2 * timestampBase + 4 < babyBearModulus)
    (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1)
    accepted.constraints accepted.states initial aligned
  intro row member
  obtain ⟨present, family⟩ := unrolled_caller_member member
  have clock := clocks row present
  simp only [Trace.Row.columns, family, CircuitLayout.columns] at clock
  exact Delegation.Caller.Proofs.caller_clock (by decide) clock.1 clock.2

/-- Exact request multiplicity covers the entire standard and split worker pools. -/
theorem unrolled_requests_complete {trace : PooledTrace babyBearModulus}
    {workers : WorkerPools babyBearModulus} {program : List RVMachineProgramEntry}
    (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    ((unrolledCallers trace).map fun row => Requests.caller row.assignment).Perm workers.fulfillments := by
  apply matching_permutation accepted.requests
  · intro call present
    obtain ⟨row, member, rfl⟩ := List.mem_map.mp present
    exact (unrolled_caller_clocks accepted initial aligned row member).2.1
  · exact worker_fulfillments_live accepted.toWorkersAccepted

/-- Caller request times are distinct occurrences on the native CPU path. -/
theorem unrolled_request_times_unique {trace : PooledTrace babyBearModulus}
    {workers : WorkerPools babyBearModulus} {program : List RVMachineProgramEntry}
    (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    (((unrolledCallers trace).map fun row => Requests.caller row.assignment).map Requests.Request.time).Nodup := by
  have clocks := Trace.Proofs.state_clock_inputs (by decide : 2 * timestampBase + 4 < babyBearModulus)
    (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1)
    accepted.constraints accepted.states initial aligned
  let rank := fun row : Trace.Row babyBearModulus PooledFamily =>
    (decodeTimestamp row.assignment row.columns.initialTime).value
  have allUnique := Trace.Proofs.state_clocks_unique (by decide : 2 * timestampBase + 4 < babyBearModulus)
    (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1)
    accepted.constraints accepted.states initial aligned
  have callerUnique : ((unrolledCallers trace).map rank).Nodup :=
    allUnique.sublist ((show (unrolledCallers trace).Sublist trace.rows from List.filter_sublist).map rank)
  simp only [List.map_map, Function.comp_def]
  apply Requests.Proofs.shifted_times_unique callerUnique
  intro row member
  obtain ⟨present, family⟩ := unrolled_caller_member member
  have clock := clocks row present
  simp only [Trace.Row.columns, family, CircuitLayout.columns] at clock
  have one : Requests.callerPort.clock.offset = 1 := rfl
  simpa only [Requests.caller, one, rank, Trace.Row.columns, family, CircuitLayout.columns,
    decodeTimestamp, timeOfPair, rawPair] using
    (Trace.Proofs.write_time (by decide : timestampBase < babyBearModulus)
      (base := rawPair row.assignment AddSub.importedConstraintsTraceColumns.initialTime)
      clock.1 clock.2 (show 1 < 4 by decide)).2

/-- Complete matching derives every standard and split worker clock bound and occurrence uniqueness. -/
theorem unrolled_worker_clocks {trace : PooledTrace babyBearModulus}
    {workers : WorkerPools babyBearModulus} {program : List RVMachineProgramEntry}
    (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    (∀ request ∈ workers.fulfillments, (timeOfPair request.time).Bounded ∧
      (timeOfPair request.time).lo + 2 < timestampBase) ∧
    (workers.fulfillments.map Requests.Request.time).Nodup := by
  have matching := unrolled_requests_complete accepted initial aligned
  refine ⟨?_, (matching.map Requests.Request.time).nodup_iff.mp
    (unrolled_request_times_unique accepted initial aligned)⟩
  intro request present
  obtain ⟨row, member, rfl⟩ := List.mem_map.mp (matching.mem_iff.mpr present)
  have clock := unrolled_caller_clocks accepted initial aligned row member
  exact ⟨clock.1, clock.2.2⟩

end Airbender.Trace.Machine.Proofs
