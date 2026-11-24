module
public import Proven.NonVacuous.DynamicCopyLoop.Model
public import Proven.WitnessCheck
public import Proven.Bigint.WitnessCheck
public import Proven.Constraints

@[expose] public section
namespace Airbender.NonVacuous.DynamicCopyLoop
open Trace Arithmetic Verification
set_option warningAsError true
set_option maxRecDepth 8192

/-- The current unified setup checks every emitted fixed-table and ROM query by its actual row index. -/
noncomputable def setupChecked : CheckedTable (ZMod babyBearModulus) :=
  staticChecked (UnifiedReduced.Setup.tableRV initial) rfl

/-- Imported CPU lookups contain thirteen range queries and five unified setup queries. -/
noncomputable def checkedTables : List (CheckedTable (ZMod babyBearModulus)) :=
  List.replicate 13 range16Checked ++ List.replicate 5 setupChecked

theorem lookup_tables :
    (FlatOperation.lookups (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.tableRV (p := babyBearModulus)
      initial))).map Lookup.table = checkedTables.map CheckedTable.table := by
  rfl

theorem timestamp_tables :
    (FlatOperation.lookups (UnifiedReduced.importedConstraintsTimestampLookups (p := babyBearModulus))).map
      Lookup.table = (List.replicate 8 timestampChecked).map CheckedTable.table := by
  rfl

/-- Every loop row satisfies its full imported description, including lookups and clock comparisons. -/
theorem machine_satisfies (index : Fin 16) : FlatOperation.ConstraintsHoldFlat (environment (machineAssignment index))
    (UnifiedReduced.clockConstraints (UnifiedReduced.Setup.tableRV initial)) := by
  apply holds_append
  · apply holds_of_checkOps lookup_tables
    fin_cases index <;> kernel_rfl
  · apply holds_of_checkOps timestamp_tables
    fin_cases index <;> kernel_rfl

/-- Both COPY workers satisfy every bigint equation and lookup, including all clock comparisons. -/
theorem worker_satisfies (index : Fin 2) : FlatOperation.ConstraintsHoldFlat (environment (workerAssignment index))
    (Bigint.clockConstraints Bigint.setupTable) := by
  apply holds_append
  · apply Bigint.holds_of_check
    fin_cases index <;> kernel_rfl
  · apply Bigint.timestamps_of_check
    fin_cases index <;> kernel_rfl

/-- The submitted worker rows satisfy their imported descriptions and execute selectors. -/
theorem workers_accepted : Trace.Machine.WorkersAccepted workers := by
  constructor
  · intro row member
    change row ∈ workerRows at member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact worker_satisfies index
  · intro row member
    change row ∈ workerRows at member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    rfl
  · intro row member
    cases member
  · intro row member
    cases member

/-- Each CPU occurrence has the exact decoded metadata of its public code location. -/
theorem decoded (index : Fin 16) : Trace.Machine.Decoded .unified
    (⟨.machine, machineAssignment index⟩ : Row babyBearModulus UnifiedFamily).decoderQuery program := by
  refine ⟨entry (codeIndex index), List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩, ?_, ?_⟩
  · fin_cases index <;> kernel_rfl
  · fin_cases index <;> kernel_rfl

/-- Both calls retain their full CSR and occurrence clock in exact request matching. -/
theorem request_matching : Delegation.Requests.Matching
    ((machineRows.filter fun row => decide (UnifiedReduced.Caller.Selected row.assignment)).map
      fun row => UnifiedReduced.Caller.request row.assignment) workers.fulfillments := by
  have same : ((machineRows.filter fun row => decide (UnifiedReduced.Caller.Selected row.assignment)).map
      fun row => UnifiedReduced.Caller.request row.assignment) = workers.fulfillments := by
    kernel_rfl
  unfold Delegation.Requests.Matching
  rw [same]
  exact List.perm_append_comm

end Airbender.NonVacuous.DynamicCopyLoop
