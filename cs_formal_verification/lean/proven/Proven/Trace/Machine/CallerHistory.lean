module
public import Proven.UnifiedReduced.RVCaller.HistoryWindow
public import Proven.Delegation.RVCallHistory

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Trace.Proofs
set_option warningAsError true

/-- Removing the caller's zero-register refreshes retains the complete native worker history. -/
theorem caller_worker_history {cells : List Cell} {events cpu worker : List MemoryAccess} {before after : RV.State}
    (permutation : events.Perm (cpu ++ worker)) (history : RVHistory cells events before after)
    (callerZero : ∀ event ∈ cpu, event.2.1 = (Cell.register 0).addressCode)
    (workerNonzero : ∀ event ∈ worker, event.2.1 ≠ (Cell.register 0).addressCode)
    (zero : ∀ event ∈ events, event.2.1 = (Cell.register 0).addressCode → memoryWord event.2.2.2 = 0) :
    (events.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)).Perm worker ∧
      RVHistory cells (events.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)) before after := by
  have empty : (cpu.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro event included selected
    exact of_decide_eq_true selected (callerZero event included)
  have complete : (worker.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)) = worker :=
    List.filter_eq_self.mpr (fun event included => decide_eq_true (workerNonzero event included))
  refine ⟨?_, rv_history_without_zero history zero⟩
  simpa only [List.filter_append, empty, complete, List.nil_append] using
    permutation.filter (fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode))

/-- Each worker port reads the cycle pre-state and writes the cycle post-state. -/
theorem caller_worker_observations {cells : List Cell} {events cpu worker : List MemoryAccess} {before after : RV.State}
    (permutation : events.Perm (cpu ++ worker)) (history : RVHistory cells events before after)
    (callerZero : ∀ event ∈ cpu, event.2.1 = (Cell.register 0).addressCode)
    (workerNonzero : ∀ event ∈ worker, event.2.1 ≠ (Cell.register 0).addressCode)
    (zero : ∀ event ∈ events, event.2.1 = (Cell.register 0).addressCode → memoryWord event.2.2.2 = 0)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (distinct : (worker.map fun event => event.2.1).Nodup) :
    ∀ event ∈ worker, ∃ cell ∈ cells, cell.addressCode = event.2.1 ∧
      cell.readRV before = some (memoryWord event.2.2.1) ∧ cell.readRV after = some (memoryWord event.2.2.2) := by
  obtain ⟨grouped, actual⟩ := caller_worker_history permutation history callerZero workerNonzero zero
  have noZero : ∀ event ∈ events.filter (fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)),
      event.2.1 ≠ (Cell.register 0).addressCode := by
    intro event included
    exact of_decide_eq_true (List.mem_filter.mp included).2
  have unique := (grouped.map (fun event => event.2.1)).nodup_iff.mpr distinct
  have observations := Delegation.Proofs.rv_atomic_observations actual aligned noZero unique
  intro event present
  exact observations event (grouped.mem_iff.mpr present)

end Airbender.Trace.Machine.Proofs
