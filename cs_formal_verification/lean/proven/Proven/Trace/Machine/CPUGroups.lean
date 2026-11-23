module
public import Proven.Trace.Machine.CPUEvents
public import Proven.Trace.Machine.EventGroups

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The unrolled CPU contribution in a cycle is exactly that row's native architectural event list. -/
theorem unrolled_cpu_window_group {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {row : Trace.Row babyBearModulus PooledFamily} (member : row ∈ trace.rows) :
    ((unrolledSteps trace).map transferEvent).filter (fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)) =
      cpuEvents row (Delegation.Caller.machinePorts row) := by
  have expanded : (unrolledSteps trace).map transferEvent =
      trace.rows.flatMap (fun source => cpuEvents source (Delegation.Caller.machinePorts source)) := by
    simp only [unrolledSteps, cpuEvents, List.map_flatMap, List.map_map, Function.comp_def]
  rw [expanded]
  apply event_group_single trace.rows Row.clock (fun source => cpuEvents source (Delegation.Caller.machinePorts source)) _
    (state_clocks_unique (by decide) (by decide) accepted.constraints accepted.states initial aligned) member
  intro source included event present
  simpa only [decide_eq_true_eq] using
    (cpu_event_window accepted.constraints accepted.states initial aligned member included
      (fun port portMember => Delegation.Caller.Proofs.machine_port_native source portMember) present)

/-- The unified CPU contribution in a cycle is exactly that row's native architectural event list. -/
theorem unified_cpu_window_group {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {row : Trace.Row babyBearModulus UnifiedFamily} (member : row ∈ trace.rows) :
    ((unifiedSteps trace).map transferEvent).filter (fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)) =
      cpuEvents row (UnifiedReduced.Caller.machinePorts row) := by
  have expanded : (unifiedSteps trace).map transferEvent =
      trace.rows.flatMap (fun source => cpuEvents source (UnifiedReduced.Caller.machinePorts source)) := by
    simp only [unifiedSteps, cpuEvents, List.map_flatMap, List.map_map, Function.comp_def]
  rw [expanded]
  apply event_group_single trace.rows Row.clock (fun source => cpuEvents source (UnifiedReduced.Caller.machinePorts source)) _
    (state_clocks_unique (by decide) (by decide) accepted.constraints accepted.states initial aligned) member
  intro source included event present
  simpa only [decide_eq_true_eq] using
    (cpu_event_window accepted.constraints accepted.states initial aligned member included
      (fun port portMember => UnifiedReduced.Caller.Proofs.rv_machine_port_native source portMember) present)

end Airbender.Trace.Machine.Proofs
