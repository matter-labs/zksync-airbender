module
public import Proven.Trace.Machine.CPUGroups
public import Proven.Trace.Machine.WorkerGroups
public import Proven.Trace.Machine.NoncallerWindows

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The unrolled caller cycle contains exactly its native architectural events. -/
theorem unrolled_caller_cycle_group {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {events : List MemoryAccess} (permutation : events.Perm ((unrolledMemory trace workers).steps.map transferEvent))
    {row : Trace.Row babyBearModulus PooledFamily} (called : row ∈ unrolledCallers trace)
    {chosen : AnyWorker babyBearModulus} (worker : chosen ∈ anyWorkers workers)
    (matched : chosen.request = Requests.caller row.assignment) :
    (events.filter fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)).Perm
      (cpuEvents row (Delegation.Caller.machinePorts row) ++ chosen.steps.map transferEvent) := by
  simpa only [List.map_append, List.filter_append, unrolledMemory,
    unrolled_cpu_window_group accepted initial aligned (unrolled_caller_member called).1,
    unrolled_worker_window_group accepted initial aligned called worker matched] using permutation.filter
      (fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4))

/-- The unrolled ordinary cycle contains exactly its native architectural events. -/
theorem unrolled_ordinary_cycle_group {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {events : List MemoryAccess} (permutation : events.Perm ((unrolledMemory trace workers).steps.map transferEvent))
    {row : Trace.Row babyBearModulus PooledFamily} (member : row ∈ trace.rows)
    (notCalled : row ∉ unrolledCallers trace) :
    (events.filter fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)).Perm
      (cpuEvents row (Delegation.Caller.machinePorts row)) := by
  simpa only [List.map_append, List.filter_append, unrolledMemory,
    unrolled_cpu_window_group accepted initial aligned member,
    unrolled_worker_window_empty accepted initial aligned member notCalled, List.append_nil] using permutation.filter
      (fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4))

/-- The unified caller cycle contains exactly its native architectural events. -/
theorem unified_caller_cycle_group {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {events : List MemoryAccess} (permutation : events.Perm ((unifiedMemory trace workers).steps.map transferEvent))
    {row : Trace.Row babyBearModulus UnifiedFamily} (called : row ∈ trace.rows.filter (fun source => decide (UnifiedReduced.Caller.Selected source.assignment)))
    {chosen : AnyWorker babyBearModulus} (worker : chosen ∈ anyWorkers workers)
    (matched : chosen.request = UnifiedReduced.Caller.request row.assignment) :
    (events.filter fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)).Perm
      (cpuEvents row (UnifiedReduced.Caller.machinePorts row) ++ chosen.steps.map transferEvent) := by
  simpa only [List.map_append, List.filter_append, unifiedMemory,
    unified_cpu_window_group accepted initial aligned (List.mem_filter.mp called).1,
    unified_worker_window_group accepted initial aligned called worker matched] using permutation.filter
      (fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4))

/-- The unified ordinary cycle contains exactly its native architectural events. -/
theorem unified_ordinary_cycle_group {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {events : List MemoryAccess} (permutation : events.Perm ((unifiedMemory trace workers).steps.map transferEvent))
    {row : Trace.Row babyBearModulus UnifiedFamily} (member : row ∈ trace.rows)
    (notCalled : row ∉ trace.rows.filter (fun source => decide (UnifiedReduced.Caller.Selected source.assignment))) :
    (events.filter fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)).Perm
      (cpuEvents row (UnifiedReduced.Caller.machinePorts row)) := by
  simpa only [List.map_append, List.filter_append, unifiedMemory,
    unified_cpu_window_group accepted initial aligned member,
    unified_worker_window_empty accepted initial aligned member notCalled, List.append_nil] using permutation.filter
      (fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4))

end Airbender.Trace.Machine.Proofs
