module
public import Proven.Trace.Machine.EventBoundary
public import Proven.Trace.Machine.CutComposition

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- All unrolled CPU and worker events lie between the public run endpoints. -/
theorem unrolled_event_bounds {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    ∀ event ∈ (unrolledMemory trace workers).steps.map transferEvent,
      (timeOfPair trace.initial.timestamp).value < event.1 ∧ event.1 ≤ (timeOfPair trace.terminal.timestamp).value := by
  have expanded : (unrolledMemory trace workers).steps.map transferEvent =
      trace.rows.flatMap (fun row => cpuEvents row (Delegation.Caller.machinePorts row)) ++ workers.steps.map transferEvent := by
    simp only [unrolledMemory, unrolledSteps, cpuEvents, List.map_append, List.map_flatMap, List.map_map, Function.comp_def]
  intro event present
  rw [expanded] at present
  rcases List.mem_append.mp present with machine | worker
  · obtain ⟨row, member, actual⟩ := List.mem_flatMap.mp machine
    exact cpu_event_boundary accepted.constraints accepted.states initial aligned member
      (fun port included => Delegation.Caller.Proofs.machine_port_native row included) actual
  · rw [← any_worker_steps, List.map_flatMap] at worker
    obtain ⟨row, member, actual⟩ := List.mem_flatMap.mp worker
    have clocks := (unrolled_worker_clocks accepted initial aligned).1
    rw [any_worker_event_time clocks member actual]
    apply unrolled_worker_boundary accepted initial aligned
    rw [← any_worker_requests]
    exact List.mem_map.mpr ⟨row, member, rfl⟩

/-- All unified CPU and worker events lie between the public run endpoints. -/
theorem unified_event_bounds {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    ∀ event ∈ (unifiedMemory trace workers).steps.map transferEvent,
      (timeOfPair trace.initial.timestamp).value < event.1 ∧ event.1 ≤ (timeOfPair trace.terminal.timestamp).value := by
  have expanded : (unifiedMemory trace workers).steps.map transferEvent =
      trace.rows.flatMap (fun row => cpuEvents row (UnifiedReduced.Caller.machinePorts row)) ++ workers.steps.map transferEvent := by
    simp only [unifiedMemory, unifiedSteps, cpuEvents, List.map_append, List.map_flatMap, List.map_map, Function.comp_def]
  intro event present
  rw [expanded] at present
  rcases List.mem_append.mp present with machine | worker
  · obtain ⟨row, member, actual⟩ := List.mem_flatMap.mp machine
    exact cpu_event_boundary accepted.constraints accepted.states initial aligned member
      (fun port included => UnifiedReduced.Caller.Proofs.rv_machine_port_native row included) actual
  · rw [← any_worker_steps, List.map_flatMap] at worker
    obtain ⟨row, member, actual⟩ := List.mem_flatMap.mp worker
    have clocks := (unified_worker_clocks accepted initial aligned).1
    rw [any_worker_event_time clocks member actual]
    apply unified_worker_boundary accepted initial aligned
    rw [← any_worker_requests]
    exact List.mem_map.mpr ⟨row, member, rfl⟩

/-- No native event precedes the initial cut, and the terminal cut contains every native event. -/
theorem history_endpoint_cuts {cells : List Cell} {events : List MemoryAccess} {initial final : RV.State}
    {lower upper : Nat} (history : RVHistory cells events initial final)
    (bounds : ∀ event ∈ events, lower < event.1 ∧ event.1 ≤ upper) :
    CutState cells events initial lower initial ∧ CutState cells events initial upper final := by
  have empty : (events.filter fun event => decide (event.1 ≤ lower)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro event member selected
    have bound := (bounds event member).1
    have current := of_decide_eq_true selected
    omega
  have complete : (events.filter fun event => decide (event.1 ≤ upper)) = events :=
    List.filter_eq_self.mpr (fun event member => decide_eq_true (bounds event member).2)
  constructor
  · change RVHistory cells (events.filter fun event => decide (event.1 ≤ lower)) initial initial
    rw [empty]
    exact .nil _
  · change RVHistory cells (events.filter fun event => decide (event.1 ≤ upper)) initial final
    rwa [complete]

end Airbender.Trace.Machine.Proofs
