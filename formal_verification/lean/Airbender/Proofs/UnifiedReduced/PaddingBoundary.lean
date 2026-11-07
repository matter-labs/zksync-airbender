import Airbender.Review.Helpers.UnifiedReduced.PaddingBoundary
import Airbender.Proofs.PaddingBoundary

namespace Airbender.UnifiedReduced.Caller.Padding.Proofs
open Trace PaddingBoundary PaddingBoundary.Proofs
set_option warningAsError true

@[simp] theorem active_callers [Fact p.Prime] (data : RequestTrace p) :
    (active data).callers = data.callers.filter fun row => decide (row.assignment row.columns.execute = 1) := by
  simp [active, RequestTrace.callers, PaddingBoundary.active, List.filter_filter, Bool.and_comm]

theorem erase_memory [Fact p.Prime] (data : RequestTrace p) (write : Bool) :
    (memoryContributions data write).filterMap (fun value => value) =
      ((active data).mixedSteps.map fun edge => if write then edge.2 else edge.1) := by
  cases write <;>
    simp [memoryContributions, machineContributions, workerContributions, erase_contributions,
      RequestTrace.mixedSteps, active, PaddingBoundary.active, Delegation.MemoryData.steps,
      List.map_flatMap, List.map_map, Function.comp_def]

theorem erase_callers [Fact p.Prime] (data : RequestTrace p) (issued : Bool) :
    (callerContributions data issued).filterMap (fun value => value) =
      ((active data).calls.map fun call => if issued then call.issued else call.empty) := by
  simp only [callerContributions, erase_contributions, flatMap_values,
    RequestTrace.calls, active_callers, List.map_map, Function.comp_def]

theorem erase_fulfillments [Fact p.Prime] (data : RequestTrace p) (issued : Bool) :
    (fulfillmentContributions data issued).filterMap (fun value => value) =
      ((active data).fulfillments.map fun call => if issued then call.issued else call.empty) := by
  simp only [fulfillmentContributions, erase_contributions, flatMap_values,
    RequestTrace.fulfillments, active, List.map_map, Function.comp_def]

theorem projected_states [Fact p.Prime] {data : RequestTrace p} (binding : Binding data) :
    ((active data).machine.initial :: (active data).machine.rows.map Trace.Row.finish).Perm
      ((active data).machine.terminal :: (active data).machine.rows.map Trace.Row.start) := by
  have matched := binding.states.filterMap (fun value => value)
  simpa only [List.filterMap_cons, erase_contributions, flatMap_values, active,
    PaddingBoundary.active] using matched

theorem projected_memory [Fact p.Prime] {data : RequestTrace p} (binding : Binding data) :
    ((active data).machine.initialMemory ++ (active data).mixedSteps.map Prod.snd).Perm
      ((active data).machine.terminalMemory ++ (active data).mixedSteps.map Prod.fst) := by
  have matched := binding.memory.filterMap (fun value => value)
  simpa only [List.filterMap_append, List.filterMap_map, Function.comp_def, List.filterMap_some,
    erase_memory, Bool.false_eq_true, ↓reduceIte, active, PaddingBoundary.active] using matched

theorem projected_requests [Fact p.Prime] {data : RequestTrace p} (binding : Binding data) :
    Delegation.Requests.Matching (active data).calls (active data).fulfillments := by
  have matched := binding.requests.filterMap (fun value => value)
  simpa only [List.filterMap_append, erase_callers, erase_fulfillments,
    Bool.false_eq_true, ↓reduceIte, Delegation.Requests.Matching] using matched

theorem projected_acceptance [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (accepted : AcceptedLayout data program) :
    MixedMemoryAccepted (active data) program := by
  refine {
    constraints := fun row member => accepted.constraints row (List.mem_of_mem_filter member)
    active := fun _ member => of_decide_eq_true (List.mem_filter.mp member).2
    states := projected_states accepted.binding
    decoded := accepted.decoded
    workerConstraints := fun row member => accepted.workerConstraints row (List.mem_of_mem_filter member)
    workerActive := fun _ member => of_decide_eq_true (List.mem_filter.mp member).2
    requests := projected_requests accepted.binding
    ordinaryDecoded := accepted.ordinaryDecoded
    memory := projected_memory accepted.binding }

theorem active_of_accepted [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (accepted : MixedMemoryAccepted data program) :
    active data = data := by
  have machines : (data.machine.rows.filter fun row => decide (row.assignment row.columns.execute = 1)) =
      data.machine.rows := List.filter_eq_self.mpr (fun row member => decide_eq_true (accepted.active row member))
  have workers : (data.workers.rows.filter fun row => decide (row.assignment row.columns.execute = 1)) =
      data.workers.rows := List.filter_eq_self.mpr (fun row member => decide_eq_true (accepted.workerActive row member))
  simp only [active, PaddingBoundary.active, machines, workers]

theorem unmasked_memory [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (accepted : MixedMemoryAccepted data program) (write : Bool) :
    memoryContributions data write = (data.mixedSteps.map fun edge => if write then edge.2 else edge.1).map some := by
  unfold memoryContributions machineContributions workerContributions
  rw [contributions_selected _ _ _ accepted.active, contributions_selected _ _ _ accepted.workerActive]
  cases write <;>
    simp [RequestTrace.mixedSteps, Delegation.MemoryData.steps, List.map_flatMap, List.map_map, Function.comp_def]

theorem unmasked_callers [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (accepted : MixedMemoryAccepted data program) (issued : Bool) :
    callerContributions data issued = (data.calls.map fun call => if issued then call.issued else call.empty).map some := by
  unfold callerContributions
  have flags : ∀ row ∈ data.callers, row.assignment row.columns.execute = 1 := by
    intro row member
    exact accepted.active row (List.mem_of_mem_filter member)
  rw [contributions_selected _ _ _ flags]
  simp only [flatMap_values, RequestTrace.calls, List.map_map, Function.comp_def]

theorem unmasked_fulfillments [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (accepted : MixedMemoryAccepted data program) (issued : Bool) :
    fulfillmentContributions data issued =
      (data.fulfillments.map fun call => if issued then call.issued else call.empty).map some := by
  unfold fulfillmentContributions
  rw [contributions_selected _ _ _ accepted.workerActive]
  simp only [flatMap_values, RequestTrace.fulfillments, List.map_map, Function.comp_def]

theorem binding_of_accepted [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (accepted : MixedMemoryAccepted data program) : Binding data := by
  refine ⟨fun row member => Or.inr (accepted.active row member),
    (fun row member => Or.inr (accepted.workerActive row member)), ?_, ?_, ?_⟩
  · rw [contributions_selected _ _ _ accepted.active, contributions_selected _ _ _ accepted.active]
    simpa only [flatMap_values, List.map_cons] using accepted.states.map some
  · rw [unmasked_memory accepted true, unmasked_memory accepted false]
    simpa only [Bool.false_eq_true, ↓reduceIte, List.map_append] using accepted.memory.map some
  · rw [unmasked_callers accepted true, unmasked_callers accepted false,
      unmasked_fulfillments accepted true, unmasked_fulfillments accepted false]
    have matching : (data.calls.map Delegation.Requests.Request.issued ++
        data.fulfillments.map Delegation.Requests.Request.empty).Perm
      (data.calls.map Delegation.Requests.Request.empty ++ data.fulfillments.map Delegation.Requests.Request.issued) :=
      accepted.requests
    simpa only [Bool.false_eq_true, ↓reduceIte, List.map_append] using matching.map some

theorem layout_of_accepted [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (accepted : MixedMemoryAccepted data program) :
    AcceptedLayout data program := by
  refine ⟨accepted.constraints, accepted.workerConstraints, ?_, ?_, binding_of_accepted accepted⟩
  · simpa only [active_of_accepted accepted] using accepted.decoded
  · simpa only [active_of_accepted accepted] using accepted.ordinaryDecoded

theorem retained_worker [Fact p.Prime] {data : RequestTrace p} {worker : Delegation.Row p}
    (member : worker ∈ data.workers.rows) (executed : worker.assignment worker.columns.execute = 1) :
    worker ∈ (active data).workers.rows := List.mem_filter.mpr ⟨member, decide_eq_true executed⟩

end Airbender.UnifiedReduced.Caller.Padding.Proofs
