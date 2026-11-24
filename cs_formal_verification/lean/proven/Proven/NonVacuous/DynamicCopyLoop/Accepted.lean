module
public import Proven.NonVacuous.DynamicCopyLoop.Rows
public import Proven.NonVacuous.DynamicCopyLoop.Frame
public import Human.Trace.Machine.Theorems

@[expose] public section
namespace Airbender.NonVacuous.DynamicCopyLoop
open Trace Arithmetic
set_option warningAsError true

/-- All sixteen CPU rows and both COPY workers meet the production logical acceptance premises. -/
theorem accepted : Trace.Machine.UnifiedAcceptance trace workers program := by
  refine ⟨workers_accepted, ?_, ?_, states, ?_, request_matching, memory_matching⟩
  · intro row member
    change row ∈ machineRows at member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact machine_satisfies index
  · intro row member
    change row ∈ machineRows at member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    rfl
  · intro row member
    change row ∈ machineRows at member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact decoded index

/-- The copy-loop program has no special5 instruction. -/
theorem no_special : Trace.Machine.NoSpecial5 program := by
  intro candidate member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  fin_cases index <;> intro impossible <;> cases impossible

/-- None of the submitted instructions selects an external input read. -/
theorem no_reads (index : Fin 16) : Trace.Machine.unifiedIsRead
    (⟨.machine, machineAssignment index⟩ : Row babyBearModulus UnifiedFamily) = false := by
  fin_cases index <;> kernel_rfl

/-- The independent input interface holds for the empty stream because the program has no reads. -/
theorem stream_ports : Trace.Machine.UnifiedStreamPorts trace initial.input := by
  intro row member selected
  change row ∈ machineRows at member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  rw [no_reads] at selected
  cases selected

/-- The complete public boot, setup, program, stream and matching premises hold for this submitted trace. -/
theorem premises :
    Trace.Machine.BootInputs .unified trace initial cells program InitsTeardowns.unifiedLayout inits ∧
    trace.rom = UnifiedReduced.Setup.tableRV initial ∧
    workers.standard.setup = Delegation.modeledSetup Keccak.Controller.rows ∧
    Trace.Machine.NoSpecial5 program ∧ Trace.Machine.UnifiedStreamPorts trace initial.input ∧
    Trace.Machine.UnifiedAcceptance trace workers program :=
  ⟨boot, rfl, rfl, no_special, stream_ports, accepted⟩

/-- The submitted witness has sixteen CPU rows and two bigint workers. -/
theorem row_counts : trace.rows.length = 16 ∧ workers.standard.rows.length = 2 ∧ workers.split.rows = [] := by
  exact ⟨by kernel_rfl, by kernel_rfl, rfl⟩

/-- The target premises have a nonempty witness with a loop and two delegation calls. -/
theorem witness : Trace.Machine.UnifiedSatisfiableClaim :=
  ⟨trace, workers, initial, cells, program, inits, premises⟩

end Airbender.NonVacuous.DynamicCopyLoop
