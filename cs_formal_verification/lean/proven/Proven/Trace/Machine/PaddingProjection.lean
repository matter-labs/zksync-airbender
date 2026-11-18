module
public import Human.Trace.Machine.Padding
public import Proven.Trace.PaddingBoundary

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Delegation PaddingBoundary PaddingBoundary.Proofs
set_option warningAsError true

/-- Erasing identity factors retains exactly the active standard and split rows. -/
theorem masked_workers_accepted {workers : WorkerPools babyBearModulus} (accepted : MaskedWorkersAccepted workers) :
    WorkersAccepted (activeWorkers workers) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro row member
    exact accepted.standardConstraints row (List.mem_of_mem_filter member)
  · intro row member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · intro row member
    exact accepted.splitConstraints row (List.mem_of_mem_filter member)
  · intro row member
    exact of_decide_eq_true (List.mem_filter.mp member).2

/-- CPU selection and caller selection commute without a PC uniqueness condition. -/
theorem active_unrolled_callers [Fact p.Prime] (trace : PooledTrace p) :
    unrolledCallers (active trace) = (unrolledCallers trace).filter fun row => decide (row.assignment row.columns.execute = 1) := by
  simp only [unrolledCallers, active, List.filter_filter]
  congr 1
  funext row
  exact Bool.and_comm _ _

/-- The unified caller selector commutes with execute-column selection. -/
theorem active_unified_callers [Fact p.Prime] (trace : UnifiedTrace p) :
    (active trace).rows.filter (fun row => decide (UnifiedReduced.Caller.Selected row.assignment)) =
      (trace.rows.filter fun row => decide (UnifiedReduced.Caller.Selected row.assignment)).filter
        fun row => decide (row.assignment row.columns.execute = 1) := by
  simp only [active, List.filter_filter]
  congr 1
  funext row
  exact Bool.and_comm _ _

/-- Identity erasure preserves the exact architectural CPU token list. -/
theorem erase_unrolled_tokens [Fact p.Prime] (trace : PooledTrace p) (token : (MemoryToken p × MemoryToken p) → MemoryToken p) :
    (maskedUnrolledTokens trace token).filterMap (fun value => value) = (unrolledSteps (active trace)).map token := by
  simp only [maskedUnrolledTokens, erase_contributions, unrolledSteps, active, List.map_flatMap, List.map_map, Function.comp_def]

/-- The same erasure preserves unified architectural tokens. -/
theorem erase_unified_tokens [Fact p.Prime] (trace : UnifiedTrace p) (token : (MemoryToken p × MemoryToken p) → MemoryToken p) :
    (maskedUnifiedTokens trace token).filterMap (fun value => value) = (unifiedSteps (active trace)).map token := by
  simp only [maskedUnifiedTokens, erase_contributions, unifiedSteps, active, List.map_flatMap, List.map_map, Function.comp_def]

/-- Worker identity erasure preserves the complete selected architectural list. -/
theorem erase_worker_tokens (workers : WorkerPools p) (token : (MemoryToken p × MemoryToken p) → MemoryToken p) :
    (maskedWorkerTokens workers token).filterMap (fun value => value) = ((activeWorkers workers).steps).map token := by
  simp only [maskedWorkerTokens, List.filterMap_append, erase_contributions, WorkerPools.steps, activeWorkers,
    Delegation.MemoryData.steps, Keccak.Split.Native.MemoryData.steps, List.map_append, List.map_flatMap]

/-- Full unrolled request tokens survive identity erasure. -/
theorem erase_unrolled_requests [Fact p.Prime] (trace : PooledTrace p) (token : Requests.Request p → MemoryToken p) :
    (maskedUnrolledRequests trace token).filterMap (fun value => value) =
      ((unrolledCallers (active trace)).map fun row => Requests.caller row.assignment).map token := by
  simp only [maskedUnrolledRequests, erase_contributions, flatMap_values, active_unrolled_callers, List.map_map, Function.comp_def]

/-- Full unified request tokens survive identity erasure. -/
theorem erase_unified_requests [Fact p.Prime] (trace : UnifiedTrace p) (token : Requests.Request p → MemoryToken p) :
    (maskedUnifiedRequests trace token).filterMap (fun value => value) =
      (((active trace).rows.filter fun row => decide (UnifiedReduced.Caller.Selected row.assignment)).map
        fun row => UnifiedReduced.Caller.request row.assignment).map token := by
  simp only [maskedUnifiedRequests, erase_contributions, flatMap_values, active_unified_callers, List.map_map, Function.comp_def]

/-- Identity erasure preserves the full standard and split fulfillment list. -/
theorem erase_worker_requests (workers : WorkerPools p) (token : Requests.Request p → MemoryToken p) :
    (maskedWorkerRequests workers token).filterMap (fun value => value) = ((activeWorkers workers).fulfillments).map token := by
  simp only [maskedWorkerRequests, List.filterMap_append, erase_contributions, flatMap_values, WorkerPools.fulfillments,
    activeWorkers, List.map_append, List.map_map, Function.comp_def]

/-- Full masked unrolled closure derives native acceptance without an inactive-row stuttering premise. -/
theorem masked_unrolled_acceptance {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : MaskedUnrolledAcceptance trace workers program) :
    UnrolledAcceptance (active trace) (activeWorkers workers) program := by
  refine { masked_workers_accepted accepted.toMaskedWorkersAccepted with
    constraints := fun row member => accepted.constraints row (List.mem_of_mem_filter member)
    active := fun row member => of_decide_eq_true (List.mem_filter.mp member).2
    decoded := accepted.decoded
    states := ?_
    requests := ?_
    memory := ?_ }
  · have matched := accepted.states.filterMap (fun value => value)
    simpa only [List.filterMap_cons, erase_contributions, flatMap_values, active] using matched
  · have matched := accepted.requests.filterMap (fun value => value)
    simpa only [List.filterMap_append, erase_unrolled_requests, erase_worker_requests, Requests.Matching] using matched
  · have matched := accepted.memory.filterMap (fun value => value)
    simpa only [List.filterMap_append, List.filterMap_map, Function.comp_def, List.filterMap_some,
      erase_unrolled_tokens, erase_worker_tokens, List.map_append, List.append_assoc, active] using matched

/-- Full masked unified closure derives native acceptance and exact request multiplicity. -/
theorem masked_unified_acceptance {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : MaskedUnifiedAcceptance trace workers program) :
    UnifiedAcceptance (active trace) (activeWorkers workers) program := by
  refine { masked_workers_accepted accepted.toMaskedWorkersAccepted with
    constraints := fun row member => accepted.constraints row (List.mem_of_mem_filter member)
    active := fun row member => of_decide_eq_true (List.mem_filter.mp member).2
    decoded := accepted.decoded
    states := ?_
    requests := ?_
    memory := ?_ }
  · have matched := accepted.states.filterMap (fun value => value)
    simpa only [List.filterMap_cons, erase_contributions, flatMap_values, active] using matched
  · have matched := accepted.requests.filterMap (fun value => value)
    simpa only [List.filterMap_append, erase_unified_requests, erase_worker_requests, Requests.Matching] using matched
  · have matched := accepted.memory.filterMap (fun value => value)
    simpa only [List.filterMap_append, List.filterMap_map, Function.comp_def, List.filterMap_some,
      erase_unified_tokens, erase_worker_tokens, List.map_append, List.append_assoc, active] using matched

end Airbender.Trace.Machine.Proofs
